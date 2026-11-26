//! Hybrid Track C + Track D Solver (`HybridGroebnerCascade`).
//!
//! Tightly couples:
//! - Phase 1 (Track C): Exact bit-packed F_2 RREF + quadratic annihilators + bounded degree-3
//!   S-polynomial closure with proof-carrying UNSAT certificate at the root.
//! - Phase 2 (Track D): Zero-allocation LDL^T / Fisher-Rao continuous marginals + single-variable
//!   confidence clamping + deterministic 1-in-3 unit-collapse cascade feeding straight back into Phase 1.
//!
//! Strictly polynomial: capped at O(n) measurement-collapse rounds and bounded deterministic restarts,
//! with ZERO recursive tree search or backtracking.

use std::time::Instant;

use crate::algebra::AlgebraicState;
use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;
use crate::marginals::MarginalWorkspace;
use crate::verifier::{verify_sat, verify_unsat_certificate, UnsatCertificate};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SolveOutcome {
    VerifiedSat,
    VerifiedUnsat,
    Unresolved,
    Overflow,
}

#[derive(Clone, Debug)]
pub struct SolveResult {
    pub outcome: SolveOutcome,
    pub assignment: Option<Vec<u8>>,
    pub unsat_cert: Option<UnsatCertificate>,
    pub unsat_cert_steps: usize,
    pub outer_rounds: usize,
    pub restarts_used: usize,
    pub runtime_sec: f64,
    pub ledger: BitLedger,
    pub termination_reason: String,
}

pub struct HybridGroebnerCascade {
    pub max_restarts: usize,
    pub marginal_burst_steps: usize,
    pub s_poly_factor: u64,
}

impl Default for HybridGroebnerCascade {
    fn default() -> Self {
        Self {
            max_restarts: 12,
            marginal_burst_steps: 18,
            s_poly_factor: 16,
        }
    }
}

impl HybridGroebnerCascade {
    pub fn solve(&self, inst: &Instance) -> SolveResult {
        let t0 = Instant::now();
        let n = inst.n_vars;
        let m = inst.m_clauses();
        let mut ledger = BitLedger::new();

        if m == 0 {
            let assign = vec![0u8; n];
            let vr = verify_sat(inst, &assign);
            return SolveResult {
                outcome: if vr.is_sat {
                    SolveOutcome::VerifiedSat
                } else {
                    SolveOutcome::Unresolved
                },
                assignment: Some(assign),
                unsat_cert: None,
                unsat_cert_steps: 0,
                outer_rounds: 0,
                restarts_used: 0,
                runtime_sec: t0.elapsed().as_secs_f64(),
                ledger,
                termination_reason: "TRIVIAL_EMPTY".to_string(),
            };
        }

        let inc = Incidence::build(inst);
        let s_poly_budget = self.s_poly_factor * ((m as u64 + 1) * (n as u64 + 1));

        // -------------------------------------------------------------------
        // PHASE 1 (ROOT): Proof-carrying Algebraic Ideal & Parity Collapse
        // -------------------------------------------------------------------
        let mut root_alg = AlgebraicState::new(n, true, &mut ledger);
        let root_ok = root_alg.init_from_instance(inst, &mut ledger)
            && root_alg.close(inst, &inc, &mut ledger, s_poly_budget);

        if !root_ok {
            let cert: UnsatCertificate = root_alg.build_certificate();
            let cert_steps = cert.steps.len();
            match verify_unsat_certificate(inst, &cert) {
                Ok(()) => {
                    return SolveResult {
                        outcome: SolveOutcome::VerifiedUnsat,
                        assignment: None,
                        unsat_cert: Some(cert),
                        unsat_cert_steps: cert_steps,
                        outer_rounds: 0,
                        restarts_used: 0,
                        runtime_sec: t0.elapsed().as_secs_f64(),
                        ledger,
                        termination_reason: "ROOT_ALGEBRAIC_UNSAT_VERIFIED".to_string(),
                    };
                }
                Err(e) => {
                    // Never emit unverified UNSAT
                    return SolveResult {
                        outcome: SolveOutcome::Unresolved,
                        assignment: None,
                        unsat_cert: None,
                        unsat_cert_steps: cert_steps,
                        outer_rounds: 0,
                        restarts_used: 0,
                        runtime_sec: t0.elapsed().as_secs_f64(),
                        ledger,
                        termination_reason: format!("UNSAT_CERT_VERIFY_FAILED: {e}"),
                    };
                }
            }
        }

        // Check if F_2 RREF particular solution already satisfies 1-in-3 SAT
        let f2_cand = root_alg.particular_f2_assignment();
        if verify_sat(inst, &f2_cand).is_sat {
            return SolveResult {
                outcome: SolveOutcome::VerifiedSat,
                assignment: Some(f2_cand),
                unsat_cert: None,
                unsat_cert_steps: 0,
                outer_rounds: 0,
                restarts_used: 0,
                runtime_sec: t0.elapsed().as_secs_f64(),
                ledger,
                termination_reason: "PHASE1_F2_DIRECT_SAT".to_string(),
            };
        }

        // Disable proof recording on speculative clones for maximum throughput
        root_alg.record_proof = false;
        root_alg.proof_steps.clear();

        // -------------------------------------------------------------------
        // PHASE 2 <-> PHASE 1: Marginal Measurement & Unit-Collapse Cascade
        // Strictly capped at O(n) rounds and bounded restarts, ZERO backtracking!
        // -------------------------------------------------------------------
        let mut ws = MarginalWorkspace::new(n, m, &inc, &mut ledger);
        let mut active_vars: Vec<usize> = Vec::with_capacity(n);
        let mut var_to_act: Vec<Option<usize>> = vec![None; n];
        let max_restarts = self.max_restarts.min(n.max(1));
        let mut total_outer_rounds = 0usize;

        for restart in 0..max_restarts {
            let mut state = root_alg.clone();
            ws.init_phases(&state.fixed, restart);

            for _round in 0..n {
                total_outer_rounds += 1;

                // Gather active unfixed variables
                active_vars.clear();
                var_to_act.fill(None);
                for v in 0..n {
                    if state.fixed[v].is_none() {
                        var_to_act[v] = Some(active_vars.len());
                        active_vars.push(v);
                    }
                }

                if active_vars.is_empty() {
                    let assign: Vec<u8> = state.fixed.iter().map(|o| o.unwrap_or(0)).collect();
                    if verify_sat(inst, &assign).is_sat {
                        return SolveResult {
                            outcome: SolveOutcome::VerifiedSat,
                            assignment: Some(assign),
                            unsat_cert: None,
                            unsat_cert_steps: 0,
                            outer_rounds: total_outer_rounds,
                            restarts_used: restart + 1,
                            runtime_sec: t0.elapsed().as_secs_f64(),
                            ledger,
                            termination_reason: "HYBRID_CASCADE_SAT".to_string(),
                        };
                    }
                    break;
                }

                // Run Phase 2 continuous marginal burst
                let use_ldlt = active_vars.len() <= 128
                    && ws.factor_active_ldlt(inst, &active_vars, &var_to_act, &mut ledger);
                ws.run_marginal_burst(
                    inst,
                    &state.fixed,
                    &active_vars,
                    use_ldlt,
                    self.marginal_burst_steps,
                    &mut ledger,
                );

                if ledger.overflow {
                    return SolveResult {
                        outcome: SolveOutcome::Overflow,
                        assignment: None,
                        unsat_cert: None,
                        unsat_cert_steps: 0,
                        outer_rounds: total_outer_rounds,
                        restarts_used: restart + 1,
                        runtime_sec: t0.elapsed().as_secs_f64(),
                        ledger,
                        termination_reason: "FLOAT_OVERFLOW".to_string(),
                    };
                }

                // Check greedy conflict-aware rounding candidate
                let cand = ws.greedy_round(&inc, &state.fixed);
                if verify_sat(inst, cand).is_sat {
                    return SolveResult {
                        outcome: SolveOutcome::VerifiedSat,
                        assignment: Some(cand.to_vec()),
                        unsat_cert: None,
                        unsat_cert_steps: 0,
                        outer_rounds: total_outer_rounds,
                        restarts_used: restart + 1,
                        runtime_sec: t0.elapsed().as_secs_f64(),
                        ledger,
                        termination_reason: "PHASE2_GREEDY_SAT".to_string(),
                    };
                }

                // Clamp single highest-confidence variable
                let Some((clamp_v, mut clamp_val)) =
                    ws.pick_highest_confidence_clamp(&active_vars, &inc)
                else {
                    break;
                };
                // Alternate parity on odd restarts for first clamp to diversify single-pass trajectories
                if restart % 2 == 1 && _round == 0 {
                    clamp_val ^= 1;
                }

                // Feed clamp straight back into Phase 1 (F_2 + degree-3 closure + unit collapse!)
                let step_s_budget = (s_poly_budget / (n as u64 + 1)).max(256);
                let ok = state.add_const(clamp_v, clamp_val, 0, &mut ledger)
                    && state.close(inst, &inc, &mut ledger, step_s_budget);

                if !ok {
                    // Contradiction after speculative clamp -> abort this pass and try next restart
                    // (ZERO backtracking tree, NEVER emit UNSAT after a speculative clamp!)
                    break;
                }

                // Check if Phase 1 F_2 particular solution now satisfies 1-in-3 SAT
                let f2_c = state.particular_f2_assignment();
                if verify_sat(inst, &f2_c).is_sat {
                    return SolveResult {
                        outcome: SolveOutcome::VerifiedSat,
                        assignment: Some(f2_c),
                        unsat_cert: None,
                        unsat_cert_steps: 0,
                        outer_rounds: total_outer_rounds,
                        restarts_used: restart + 1,
                        runtime_sec: t0.elapsed().as_secs_f64(),
                        ledger,
                        termination_reason: "HYBRID_F2_REDUCED_SAT".to_string(),
                    };
                }
            }
        }

        SolveResult {
            outcome: SolveOutcome::Unresolved,
            assignment: None,
            unsat_cert: None,
            unsat_cert_steps: 0,
            outer_rounds: total_outer_rounds,
            restarts_used: max_restarts,
            runtime_sec: t0.elapsed().as_secs_f64(),
            ledger,
            termination_reason: "MAX_POLYNOMIAL_RESTARTS_EXHAUSTED".to_string(),
        }
    }
}
