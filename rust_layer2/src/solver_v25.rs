//! Layer 2.5 Solver (`GadgetSPCascade`):
//! - Upgrade 1: Local Gadget Elimination (peeling low-degree auxiliary clusters -> exact F_2 affine equations)
//! - Phase 1: Bit-packed F_2 RREF + quadratic annihilators + bounded degree-3 S-polynomial closure
//! - Upgrade 2: 1-in-3 Survey Propagation (cavity marginals) + Nogood Repulsion (zero recursive backtracking)

use std::time::Instant;

use crate::algebra::AlgebraicState;
use crate::cutting_planes::run_cutting_planes_dual;
use crate::gadget::peel_gadgets_and_inject_f2;
use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;
use crate::solver::{SolveOutcome, SolveResult};
use crate::sp::{NogoodStore, SpWorkspace};
use crate::verifier::{verify_sat, verify_unsat_certificate, UnsatCertificate};

pub struct GadgetSPCascade {
    pub max_restarts: usize,
    pub max_sp_sweeps: usize,
    pub s_poly_factor: u64,
    pub enable_cutting_planes: bool,
    pub enable_flp_and_nogoods: bool,
}

impl Default for GadgetSPCascade {
    fn default() -> Self {
        Self {
            max_restarts: 24,
            max_sp_sweeps: 32,
            s_poly_factor: 16,
            enable_cutting_planes: false,
            enable_flp_and_nogoods: false,
        }
    }
}

impl GadgetSPCascade {
    /// Layer 2.75 configuration: Gadget Peeling + F_2/Deg-3 Groebner + Bounded Z-Cutting-Planes + 1-in-3 SP.
    pub fn layer275() -> Self {
        Self {
            enable_cutting_planes: true,
            enable_flp_and_nogoods: false,
            ..Self::default()
        }
    }

    /// Layer 2.8 configuration: Layer 2.75 + Root 1-Step Failed-Literal Elimination +
    /// Cross-Restart Implication Nogood Learning + Cluster-Guided WalkSAT Island Polish.
    pub fn layer28() -> Self {
        Self {
            enable_cutting_planes: true,
            enable_flp_and_nogoods: true,
            ..Self::default()
        }
    }
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
        // PHASE 0 + 1 (ROOT): Algebraic Init -> Local Gadget Peeling -> F_2 + Deg-3 Closure
        // -------------------------------------------------------------------
        let mut root_alg = AlgebraicState::new(n, true, &mut ledger);
        let mut root_ok = root_alg.init_from_instance(inst, &mut ledger)
            && root_alg.close(inst, &inc, &mut ledger, s_poly_budget / 2);

        let mut gadget_eqs = 0usize;
        let mut cp_unsat = false;
        let mut flp_unsat = false;

        // Alternating F_2 Gadget-Peel/RREF <-> Z Cutting-Planes fixpoint loop (bounded <= 3 rounds)
        for _fp_round in 0..3 {
            if !root_ok {
                break;
            }
            let prev_fixed = root_alg.fixed.iter().filter(|o| o.is_some()).count();
            let prev_pivots = root_alg.pivot_cols.len();

            let (g_ok, n_inj) = peel_gadgets_and_inject_f2(inst, &inc, &mut root_alg, &mut ledger);
            gadget_eqs += n_inj;
            root_ok = g_ok && root_alg.close(inst, &inc, &mut ledger, s_poly_budget);

            if root_ok && self.enable_cutting_planes {
                match run_cutting_planes_dual(inst, &mut root_alg, &mut ledger) {
                    Err(()) => {
                        root_ok = false;
                        cp_unsat = true;
                        break;
                    }
                    Ok(forced_units) => {
                        let _ = forced_units;
                    }
                }
            }

            let cur_fixed = root_alg.fixed.iter().filter(|o| o.is_some()).count();
            let cur_pivots = root_alg.pivot_cols.len();
            if cur_fixed == prev_fixed && cur_pivots == prev_pivots {
                break;
            }
        }

        if root_ok && self.enable_flp_and_nogoods {
            let (flp_ok, flp_elims) =
                root_alg.run_root_failed_literal_elim(inst, &inc, &mut ledger, s_poly_budget, 4);
            if !flp_ok {
                root_ok = false;
                flp_unsat = true;
            } else if flp_elims > 0 && self.enable_cutting_planes {
                if run_cutting_planes_dual(inst, &mut root_alg, &mut ledger).is_err() {
                    root_ok = false;
                    cp_unsat = true;
                }
            }
        }

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
                        termination_reason: if flp_unsat {
                            "FAILED_LITERAL_ELIM_UNSAT_VERIFIED".to_string()
                        } else if cp_unsat {
                            "CUTTING_PLANES_Z_UNSAT_VERIFIED".to_string()
                        } else if gadget_eqs > 0 {
                            "GADGET_PEEL_F2_UNSAT_VERIFIED".to_string()
                        } else {
                            "ROOT_ALGEBRAIC_UNSAT_VERIFIED".to_string()
                        },
                    };
                }
                Err(e) => {
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

        // Check if Phase 1 F_2 particular solution already satisfies 1-in-3 SAT
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
                termination_reason: "PHASE1_GADGET_F2_DIRECT_SAT".to_string(),
            };
        }

        // Disable proof recording on speculative clones
        root_alg.record_proof = false;
        root_alg.proof_steps.clear();

        // -------------------------------------------------------------------
        // PHASE 2 (1-in-3 SURVEY PROPAGATION + NOGOOD REPULSION) <-> PHASE 1
        // Strictly capped at O(n) restarts & O(n) rounds, ZERO recursive backtracking!
        // -------------------------------------------------------------------
        let mut sp = SpWorkspace::new(n, m, &mut ledger);
        let mut nogoods = NogoodStore::new(n);
        let mut active_vars: Vec<usize> = Vec::with_capacity(n);
        let mut clamps: Vec<(usize, u8)> = Vec::with_capacity(n);
        let max_restarts = self.max_restarts.min(n.max(1));
        let mut total_outer_rounds = 0usize;

        for restart in 0..max_restarts {
            let mut state = root_alg.clone();
            sp.init_surveys(restart);
            clamps.clear();

            for round in 0..n {
                total_outer_rounds += 1;

                active_vars.clear();
                for v in 0..n {
                    if state.fixed[v].is_none() {
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
                            termination_reason: "GADGET_SP_CASCADE_SAT".to_string(),
                        };
                    }
                    nogoods.record_conflict(&clamps);
                    break;
                }

                // Layer 2.8: Propagate any learned unit nogood before SP sweeps
                if self.enable_flp_and_nogoods {
                    let mut ng_ok = true;
                    while let Some((nv, nval)) = nogoods.find_unit_propagation(&state.fixed) {
                        let step_s_budget = (s_poly_budget / (n as u64 + 1)).max(256);
                        if !(state.add_const(nv, nval, 0, &mut ledger)
                            && state.close(inst, &inc, &mut ledger, step_s_budget))
                        {
                            ng_ok = false;
                            break;
                        }
                    }
                    if !ng_ok {
                        nogoods.record_conflict(&clamps);
                        break;
                    }
                    active_vars.clear();
                    for v in 0..n {
                        if state.fixed[v].is_none() {
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
                                termination_reason: "NOGOOD_UNIT_CASCADE_SAT".to_string(),
                            };
                        }
                        nogoods.record_conflict(&clamps);
                        break;
                    }
                }

                // Run damped 1-in-3 Survey Propagation sweeps
                let sweeps = if round == 0 {
                    self.max_sp_sweeps
                } else {
                    (self.max_sp_sweeps / 2).max(8)
                };
                sp.run_sp(inst, &state.fixed, &nogoods, sweeps, &mut ledger);

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

                // Check SP-guided greedy conflict-aware rounding
                let cand = sp.greedy_round(&inc, &state.fixed);
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
                        termination_reason: "SP_GREEDY_SAT".to_string(),
                    };
                }

                // Layer 2.8: Cluster-Guided WalkSAT Island Polish when >= 70% frozen
                if self.enable_flp_and_nogoods && active_vars.len() * 10 <= n * 3 {
                    let seed = (restart as u64).wrapping_mul(1009).wrapping_add(round as u64);
                    if let Some(polished) =
                        sp.walksat_island_polish(inst, &inc, &state.fixed, seed, &mut ledger)
                    {
                        if verify_sat(inst, &polished).is_sat {
                            return SolveResult {
                                outcome: SolveOutcome::VerifiedSat,
                                assignment: Some(polished),
                                unsat_cert: None,
                                unsat_cert_steps: 0,
                                outer_rounds: total_outer_rounds,
                                restarts_used: restart + 1,
                                runtime_sec: t0.elapsed().as_secs_f64(),
                                ledger,
                                termination_reason: "SP_WALKSAT_ISLAND_SAT".to_string(),
                            };
                        }
                    }
                }

                // Clamp single highest frozen-bias variable (with nogood repulsion)
                let Some((clamp_v, clamp_val)) =
                    sp.pick_frozen_clamp(&active_vars, &inc, &nogoods, &clamps)
                else {
                    break;
                };
                clamps.push((clamp_v, clamp_val));

                // Feed clamp straight back into Phase 1 (unit collapse + F_2 + deg-3 closure)
                let step_s_budget = (s_poly_budget / (n as u64 + 1)).max(256);
                let ok = state.add_const(clamp_v, clamp_val, 0, &mut ledger)
                    && state.close(inst, &inc, &mut ledger, step_s_budget);

                if !ok {
                    // Record nogood repulsion and restart (ZERO backtracking tree!)
                    nogoods.record_conflict(&clamps);
                    if self.enable_flp_and_nogoods && !clamps.is_empty() {
                        // Extract minimal binary/ternary conflicting tail subset against root_alg
                        let tail_len = clamps.len().min(3);
                        let tail = &clamps[clamps.len() - tail_len..];
                        let mut test_alg = root_alg.clone();
                        let mut tail_ok = true;
                        for &(tv, tval) in tail {
                            if !(test_alg.add_const(tv, tval, 0, &mut ledger)
                                && test_alg.close(inst, &inc, &mut ledger, step_s_budget))
                            {
                                tail_ok = false;
                                break;
                            }
                        }
                        if !tail_ok {
                            nogoods.add_nogood_clause(tail.to_vec());
                        }
                    }
                    break;
                }

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
                        termination_reason: "GADGET_SP_F2_REDUCED_SAT".to_string(),
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
            termination_reason: "MAX_SP_RESTARTS_EXHAUSTED".to_string(),
        }
    }
}
