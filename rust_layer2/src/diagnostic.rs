//! Isolated Diagnostic Ground-Truth Oracle & SP Failure-Mode Profiler.
//!
//! STRICTLY FOR DIAGNOSTIC GROUND-TRUTH LABELING (`--diagnose-frontier`) ONLY.
//! Never imported by `solver.rs`, `solver_v25.rs`, `algebra.rs`, `sp.rs`, or `cutting_planes.rs`.

use std::collections::HashSet;
use std::time::Instant;

use crate::algebra::AlgebraicState;
use crate::gadget::peel_gadgets_and_inject_f2;
use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;
use crate::sp::{NogoodStore, SpWorkspace};
use crate::verifier::verify_sat;

#[derive(Clone, Debug)]
pub struct FrontierDiagnosis {
    pub instance_id: String,
    pub n_vars: usize,
    pub m_clauses: usize,
    pub ground_truth: String, // "SAT", "UNSAT", or "ORACLE_TIMEOUT"
    pub oracle_nodes: u64,
    pub oracle_time_sec: f64,
    pub root_fixed_frac: f64,
    pub root_sp_frozen_frac: f64,
    pub root_sp_water_frac: f64,
    pub avg_depth_before_conflict: f64,
    pub max_depth_before_conflict: usize,
    pub unique_conflict_vars: usize,
    pub total_restarts_profiled: usize,
}

/// Bounded exact DPLL diagnostic oracle (strictly for ground-truth labeling, never used in solver).
pub fn diagnose_ground_truth(inst: &Instance, max_nodes: u64) -> (String, u64, f64) {
    let t0 = Instant::now();
    let n = inst.n_vars;
    let inc = Incidence::build(inst);
    let mut assign: Vec<Option<u8>> = vec![None; n];
    let mut trail: Vec<usize> = Vec::with_capacity(n);
    let mut nodes = 0u64;

    fn propagate(
        inst: &Instance,
        inc: &Incidence,
        assign: &mut [Option<u8>],
        trail: &mut Vec<usize>,
        seed_clauses: &[usize],
    ) -> bool {
        let mut queue: Vec<usize> = seed_clauses.to_vec();
        while let Some(c_idx) = queue.pop() {
            let [a, b, c] = inst.clauses[c_idx];
            let mut sum = 0u8;
            let mut unfixed = [0usize; 3];
            let mut ucnt = 0usize;
            for &v in &[a, b, c] {
                match assign[v] {
                    Some(val) => sum += val,
                    None => {
                        unfixed[ucnt] = v;
                        ucnt += 1;
                    }
                }
            }
            if sum > 1 {
                return false;
            }
            if sum == 1 {
                for i in 0..ucnt {
                    let v = unfixed[i];
                    if assign[v].is_none() {
                        assign[v] = Some(0);
                        trail.push(v);
                        for &(nc, _) in inc.clauses_of(v) {
                            queue.push(nc);
                        }
                    } else if assign[v] == Some(1) {
                        return false;
                    }
                }
            } else if ucnt == 0 {
                return false;
            } else if ucnt == 1 {
                let v = unfixed[0];
                if assign[v].is_none() {
                    assign[v] = Some(1);
                    trail.push(v);
                    for &(nc, _) in inc.clauses_of(v) {
                        queue.push(nc);
                    }
                } else if assign[v] == Some(0) {
                    return false;
                }
            } else if ucnt == 2 && unfixed[0] == unfixed[1] {
                // (v, v, 0) => v = 0, but sum == 0 so clause fails
                return false;
            } else if ucnt == 3 && (unfixed[0] == unfixed[1] || unfixed[0] == unfixed[2] || unfixed[1] == unfixed[2]) {
                let dup = if unfixed[0] == unfixed[1] || unfixed[0] == unfixed[2] {
                    unfixed[0]
                } else {
                    unfixed[1]
                };
                if unfixed[0] == unfixed[1] && unfixed[1] == unfixed[2] {
                    return false;
                }
                if assign[dup].is_none() {
                    assign[dup] = Some(0);
                    trail.push(dup);
                    for &(nc, _) in inc.clauses_of(dup) {
                        queue.push(nc);
                    }
                }
            }
        }
        true
    }

    fn dfs(
        inst: &Instance,
        inc: &Incidence,
        assign: &mut [Option<u8>],
        trail: &mut Vec<usize>,
        nodes: &mut u64,
        max_nodes: u64,
    ) -> Option<bool> {
        *nodes += 1;
        if *nodes > max_nodes {
            return None;
        }
        // Pick highest-degree unfixed variable
        let mut best_v = None;
        let mut best_deg = 0u32;
        for v in 0..inst.n_vars {
            if assign[v].is_none() && (best_v.is_none() || inc.degrees[v] > best_deg) {
                best_deg = inc.degrees[v];
                best_v = Some(v);
            }
        }
        let Some(v) = best_v else {
            let sol: Vec<u8> = assign.iter().map(|o| o.unwrap_or(0)).collect();
            return Some(verify_sat(inst, &sol).is_sat);
        };

        for val in [1u8, 0u8] {
            let mark = trail.len();
            assign[v] = Some(val);
            trail.push(v);
            let seeds: Vec<usize> = inc.clauses_of(v).iter().map(|&(c, _)| c).collect();
            if propagate(inst, inc, assign, trail, &seeds) {
                match dfs(inst, inc, assign, trail, nodes, max_nodes) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => return None,
                }
            }
            while trail.len() > mark {
                let pv = trail.pop().unwrap();
                assign[pv] = None;
            }
        }
        Some(false)
    }

    let all_clauses: Vec<usize> = (0..inst.m_clauses()).collect();
    if !propagate(inst, &inc, &mut assign, &mut trail, &all_clauses) {
        return ("UNSAT".to_string(), nodes, t0.elapsed().as_secs_f64());
    }
    let label = match dfs(inst, &inc, &mut assign, &mut trail, &mut nodes, max_nodes) {
        Some(true) => "SAT",
        Some(false) => "UNSAT",
        None => "ORACLE_TIMEOUT",
    };
    (label.to_string(), nodes, t0.elapsed().as_secs_f64())
}

/// Profile SP cavity behavior and conflict depth across 24 restarts on a frontier instance.
pub fn profile_frontier_instance(inst: &Instance) -> FrontierDiagnosis {
    let (gt, oracle_nodes, oracle_time_sec) = diagnose_ground_truth(inst, 2_000_000);
    let n = inst.n_vars;
    let m = inst.m_clauses();
    let inc = Incidence::build(inst);
    let mut ledger = BitLedger::new();
    let s_poly_budget = 16 * ((m as u64 + 1) * (n as u64 + 1));

    let mut root_alg = AlgebraicState::new(n, false, &mut ledger);
    let _ = root_alg.init_from_instance(inst, &mut ledger)
        && root_alg.close(inst, &inc, &mut ledger, s_poly_budget / 2);
    let (g_ok, _) = peel_gadgets_and_inject_f2(inst, &inc, &mut root_alg, &mut ledger);
    if g_ok {
        let _ = root_alg.close(inst, &inc, &mut ledger, s_poly_budget);
    }

    let root_fixed = root_alg.fixed.iter().filter(|o| o.is_some()).count();
    let root_fixed_frac = (root_fixed as f64) / (n as f64);

    let mut sp = SpWorkspace::new(n, m, &mut ledger);
    let mut nogoods = NogoodStore::new(n);
    sp.init_surveys(0);
    sp.run_sp(inst, &root_alg.fixed, &nogoods, 32, &mut ledger);

    let mut frozen_cnt = 0usize;
    let mut water_cnt = 0usize;
    let mut unfixed_cnt = 0usize;
    for v in 0..n {
        if root_alg.fixed[v].is_none() {
            unfixed_cnt += 1;
            if (sp.p1[v] - sp.p0[v]).abs() > 0.5 {
                frozen_cnt += 1;
            }
            if sp.p_star[v] > 0.5 {
                water_cnt += 1;
            }
        }
    }
    let denom = unfixed_cnt.max(1) as f64;
    let root_sp_frozen_frac = (frozen_cnt as f64) / denom;
    let root_sp_water_frac = (water_cnt as f64) / denom;

    let restarts = 24usize;
    let mut sum_depth = 0usize;
    let mut max_depth = 0usize;
    let mut conflict_vars: HashSet<usize> = HashSet::new();
    let mut active_vars = Vec::with_capacity(n);
    let mut clamps = Vec::with_capacity(n);

    for r in 0..restarts {
        let mut st = root_alg.clone();
        sp.init_surveys(r);
        clamps.clear();
        let mut depth = 0usize;
        for round in 0..n {
            active_vars.clear();
            for v in 0..n {
                if st.fixed[v].is_none() {
                    active_vars.push(v);
                }
            }
            if active_vars.is_empty() {
                break;
            }
            sp.run_sp(inst, &st.fixed, &nogoods, if round == 0 { 24 } else { 8 }, &mut ledger);
            let Some((cv, cval)) = sp.pick_frozen_clamp(&active_vars, &inc, &nogoods, &clamps) else {
                break;
            };
            clamps.push((cv, cval));
            depth += 1;
            let step_budget = (s_poly_budget / (n as u64 + 1)).max(256);
            let ok = st.add_const(cv, cval, 0, &mut ledger)
                && st.close(inst, &inc, &mut ledger, step_budget);
            if !ok {
                conflict_vars.insert(cv);
                nogoods.record_conflict(&clamps);
                break;
            }
        }
        sum_depth += depth;
        if depth > max_depth {
            max_depth = depth;
        }
    }

    FrontierDiagnosis {
        instance_id: inst.id.clone(),
        n_vars: n,
        m_clauses: m,
        ground_truth: gt,
        oracle_nodes,
        oracle_time_sec,
        root_fixed_frac,
        root_sp_frozen_frac,
        root_sp_water_frac,
        avg_depth_before_conflict: (sum_depth as f64) / (restarts as f64),
        max_depth_before_conflict: max_depth,
        unique_conflict_vars: conflict_vars.len(),
        total_restarts_profiled: restarts,
    }
}
