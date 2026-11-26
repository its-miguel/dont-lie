//! Upgrade 2 (Layer 2.5): 1-in-3 Survey Propagation (Cavity Marginals) + Nogood Repulsion.
//!
//! Separates frozen cluster biases (P_i^0, P_i^1) from unconstrained "*" ("water") states P_i^*
//! via damped cavity message passing capped at O(n) sweeps, plus lightweight nogood repulsion
//! across polynomial restarts (strictly zero recursive tree backtracking).

use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;

/// Lightweight nogood store recording conflicting literal clamps from failed single-pass restarts,
/// plus learned binary/ternary nogood clauses (Layer 2.8) injected into the SP factor graph.
#[derive(Clone, Debug, Default)]
pub struct NogoodStore {
    /// Per-variable repulsion multipliers (penalize values that repeatedly caused dead ends).
    pub repulse_0: Vec<f64>,
    pub repulse_1: Vec<f64>,
    /// Recorded small conflicting prefixes (lit = (var, val)) to avoid exact repeats.
    pub failed_prefixes: Vec<Vec<(usize, u8)>>,
    /// Learned compact nogood clauses (each entry is a forbidden conjunction of 1..=3 literals).
    pub nogood_clauses: Vec<Vec<(usize, u8)>>,
}

impl NogoodStore {
    pub fn new(n: usize) -> Self {
        Self {
            repulse_0: vec![1.0; n],
            repulse_1: vec![1.0; n],
            failed_prefixes: Vec::new(),
            nogood_clauses: Vec::new(),
        }
    }

    /// Record a compact learned nogood clause (forbidden conjunction of 1..=3 literals).
    pub fn add_nogood_clause(&mut self, mut clause: Vec<(usize, u8)>) {
        if clause.is_empty() || clause.len() > 3 || self.nogood_clauses.len() >= 256 {
            return;
        }
        clause.sort_unstable();
        clause.dedup();
        if !self.nogood_clauses.contains(&clause) {
            self.nogood_clauses.push(clause);
        }
    }

    /// Return any unit nogood forced by the current `fixed` assignment:
    /// if all literals except one in a learned nogood are fixed to their forbidden values,
    /// returns `Some((v, forbidden_val ^ 1))` for the remaining unfixed literal.
    pub fn find_unit_propagation(&self, fixed: &[Option<u8>]) -> Option<(usize, u8)> {
        for ng in &self.nogood_clauses {
            let mut unfixed_lit: Option<(usize, u8)> = None;
            let mut all_others_match = true;
            for &(v, forb) in ng {
                match fixed[v] {
                    Some(val) if val == forb => {}
                    Some(_) => {
                        all_others_match = false;
                        break;
                    }
                    None => {
                        if unfixed_lit.is_some() {
                            all_others_match = false;
                            break;
                        }
                        unfixed_lit = Some((v, forb));
                    }
                }
            }
            if all_others_match {
                if let Some((v, forb)) = unfixed_lit {
                    return Some((v, forb ^ 1));
                }
            }
        }
        None
    }

    /// Record a failed clamping trajectory; penalize the most recent (blamed) clamped literals.
    pub fn record_conflict(&mut self, clamps: &[(usize, u8)]) {
        if clamps.is_empty() {
            return;
        }
        // Apply decaying repulsion to the last 3 clamped literals (strongest on the final blamed literal)
        let len = clamps.len();
        for (offset, &(v, val)) in clamps.iter().rev().take(3).enumerate() {
            let decay = match offset {
                0 => 0.45,
                1 => 0.72,
                _ => 0.85,
            };
            if val == 0 {
                self.repulse_0[v] = (self.repulse_0[v] * decay).max(0.05);
            } else {
                self.repulse_1[v] = (self.repulse_1[v] * decay).max(0.05);
            }
        }
        let prefix_len = len.min(4);
        self.failed_prefixes.push(clamps[..prefix_len].to_vec());
    }

    /// Check whether clamping `(v, val)` as the next step in `current_clamps` would
    /// exactly reproduce a previously failed short prefix.
    pub fn would_repeat_failed(&self, current_clamps: &[(usize, u8)], v: usize, val: u8) -> bool {
        let next_len = current_clamps.len() + 1;
        for pref in &self.failed_prefixes {
            if pref.len() == next_len
                && pref[..current_clamps.len()] == *current_clamps
                && pref[next_len - 1] == (v, val)
            {
                return true;
            }
        }
        false
    }
}

/// Zero-allocation reusable workspace for 1-in-3 Survey Propagation.
pub struct SpWorkspace {
    pub n: usize,
    pub m: usize,
    /// Warning surveys from clause c to its 3 slots (0, 1, 2): u0 = forces 0, u1 = forces 1.
    pub u0: Vec<[f64; 3]>,
    pub u1: Vec<[f64; 3]>,
    /// Global variable cavity marginals (P_i^0, P_i^1, P_i^*).
    pub p0: Vec<f64>,
    pub p1: Vec<f64>,
    pub p_star: Vec<f64>,
    /// Precomputed per-variable products over all incident clauses for O(1) cavity exclusion.
    prod_not1: Vec<f64>,
    prod_not0: Vec<f64>,
    prod_star: Vec<f64>,
    /// Scratch buffers for greedy conflict-aware rounding.
    order: Vec<usize>,
    clause_hits: Vec<u8>,
    cand: Vec<u8>,
}

impl SpWorkspace {
    pub fn new(n: usize, m: usize, ledger: &mut BitLedger) -> Self {
        let bytes = (m * 6 + n * 6) * 8 + n * 8 + m + n;
        ledger.record_mem_alloc(bytes);
        Self {
            n,
            m,
            u0: vec![[0.0; 3]; m],
            u1: vec![[0.0; 3]; m],
            p0: vec![0.0; n],
            p1: vec![0.0; n],
            p_star: vec![1.0; n],
            prod_not1: vec![1.0; n],
            prod_not0: vec![1.0; n],
            prod_star: vec![1.0; n],
            order: (0..n).collect(),
            clause_hits: vec![0u8; m],
            cand: vec![0u8; n],
        }
    }

    /// Initialize clause-to-variable warning surveys deterministically for a given restart.
    pub fn init_surveys(&mut self, restart_idx: usize) {
        let mut state = 0x517cc1b727220a95u64.wrapping_add((restart_idx as u64).wrapping_mul(0x9e3779b97f4a7c15));
        let mut next_unit = || -> f64 {
            state = state.wrapping_add(0x9e3779b97f4a7c15);
            let mut z = state;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
            z ^= z >> 31;
            ((z >> 11) as f64) * (1.0 / ((1u64 << 53) as f64))
        };
        for c in 0..self.m {
            for s in 0..3 {
                // Keep initial warnings modest so SP starts in a well-conditioned cavity basin
                let a = 0.05 + 0.25 * next_unit();
                let b = 0.05 + 0.15 * next_unit();
                self.u0[c][s] = a;
                self.u1[c][s] = b;
            }
        }
    }

    /// Run damped 1-in-3 Survey Propagation sweeps on the active (unfixed) subproblem.
    /// Returns the number of sweeps executed.
    pub fn run_sp(
        &mut self,
        inst: &Instance,
        fixed: &[Option<u8>],
        nogoods: &NogoodStore,
        max_sweeps: usize,
        ledger: &mut BitLedger,
    ) -> usize {
        let damping = 0.65;
        let eps = 1e-12;
        let tol = 1e-4;
        let mut sweeps_done = 0usize;

        for sweep in 0..max_sweeps {
            sweeps_done = sweep + 1;

            // 1. Compute full per-variable cavity products across all active clauses
            for v in 0..self.n {
                self.prod_not1[v] = 1.0;
                self.prod_not0[v] = 1.0;
                self.prod_star[v] = 1.0;
            }

            for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
                // Skip satisfied clauses (any literal fixed to 1)
                if fixed[a] == Some(1) || fixed[b] == Some(1) || fixed[c] == Some(1) {
                    continue;
                }
                let lits = [a, b, c];
                for s in 0..3 {
                    let v = lits[s];
                    if fixed[v].is_none() {
                        let u0 = self.u0[c_idx][s];
                        let u1 = self.u1[c_idx][s];
                        let w_not1 = (1.0 - u1).max(eps);
                        let w_not0 = (1.0 - u0).max(eps);
                        let w_star = (1.0 - u0 - u1).max(eps);
                        self.prod_not1[v] *= w_not1;
                        self.prod_not0[v] *= w_not0;
                        self.prod_star[v] *= w_star;
                    }
                }
            }

            // 2. Update clause-to-variable warning surveys (u0, u1) using exact 9-state 1-in-3 cavity rule
            let mut max_diff = 0.0f64;
            for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
                if fixed[a] == Some(1) || fixed[b] == Some(1) || fixed[c] == Some(1) {
                    self.u0[c_idx] = [0.0; 3];
                    self.u1[c_idx] = [0.0; 3];
                    continue;
                }
                let lits = [a, b, c];
                // Compute incoming cavity marginals pi[s] = (pi0, pi1, pi_star) for each slot s
                let mut pi = [[0.0f64; 3]; 3];
                for s in 0..3 {
                    let v = lits[s];
                    match fixed[v] {
                        Some(0) => pi[s] = [1.0, 0.0, 0.0],
                        Some(_) => pi[s] = [0.0, 1.0, 0.0],
                        None => {
                            let u0 = self.u0[c_idx][s];
                            let u1 = self.u1[c_idx][s];
                            let p_n1 = self.prod_not1[v] / (1.0 - u1).max(eps);
                            let p_n0 = self.prod_not0[v] / (1.0 - u0).max(eps);
                            let p_st = self.prod_star[v] / (1.0 - u0 - u1).max(eps);
                            let w0 = (p_n1 - p_st).max(0.0) * nogoods.repulse_0[v];
                            let w1 = (p_n0 - p_st).max(0.0) * nogoods.repulse_1[v];
                            let ws = p_st.max(eps);
                            let z = w0 + w1 + ws;
                            pi[s] = [w0 / z, w1 / z, ws / z];
                        }
                    }
                }

                // Exact 9-state cavity projection onto each unfixed slot
                for s in 0..3 {
                    let v = lits[s];
                    if fixed[v].is_some() {
                        continue;
                    }
                    let (j, k) = match s {
                        0 => (1, 2),
                        1 => (0, 2),
                        _ => (0, 1),
                    };
                    let (j0, j1, js) = (pi[j][0], pi[j][1], pi[j][2]);
                    let (k0, k1, ks) = (pi[k][0], pi[k][1], pi[k][2]);

                    // Consistent pairs exclude (1, 1):
                    // (0, 0) => forces v = 1
                    let raw_u1 = j0 * k0;
                    // (1, 0), (0, 1), (1, *), (*, 1) => forces v = 0
                    let raw_u0 = j1 * (k0 + ks) + k1 * (j0 + js);
                    // (0, *), (*, 0), (*, *) => leaves v = *
                    let raw_us = j0 * ks + js * k0 + js * ks;
                    let norm = (raw_u1 + raw_u0 + raw_us).max(eps);

                    let new_u0 = (raw_u0 / norm).clamp(0.0, 1.0 - 1e-9);
                    let new_u1 = (raw_u1 / norm).clamp(0.0, (1.0 - new_u0 - 1e-9).max(0.0));

                    let old_u0 = self.u0[c_idx][s];
                    let old_u1 = self.u1[c_idx][s];
                    let upd_u0 = damping * new_u0 + (1.0 - damping) * old_u0;
                    let upd_u1 = damping * new_u1 + (1.0 - damping) * old_u1;

                    let diff = (upd_u0 - old_u0).abs().max((upd_u1 - old_u1).abs());
                    if diff > max_diff {
                        max_diff = diff;
                    }
                    self.u0[c_idx][s] = upd_u0;
                    self.u1[c_idx][s] = upd_u1;
                    ledger.fisher_rao_ops += 18;
                    ledger.record_float(upd_u0);
                    ledger.record_float(upd_u1);
                }
            }

            if max_diff < tol {
                break;
            }
        }

        // 3. Compute final global variable cavity biases (P_i^0, P_i^1, P_i^*)
        for v in 0..self.n {
            match fixed[v] {
                Some(0) => {
                    self.p0[v] = 1.0;
                    self.p1[v] = 0.0;
                    self.p_star[v] = 0.0;
                }
                Some(_) => {
                    self.p0[v] = 0.0;
                    self.p1[v] = 1.0;
                    self.p_star[v] = 0.0;
                }
                None => {
                    let w0 = (self.prod_not1[v] - self.prod_star[v]).max(0.0) * nogoods.repulse_0[v];
                    let w1 = (self.prod_not0[v] - self.prod_star[v]).max(0.0) * nogoods.repulse_1[v];
                    let ws = self.prod_star[v].max(eps);
                    let z = w0 + w1 + ws;
                    self.p0[v] = w0 / z;
                    self.p1[v] = w1 / z;
                    self.p_star[v] = ws / z;
                    ledger.record_float(self.p0[v]);
                    ledger.record_float(self.p1[v]);
                }
            }
        }

        // 4. Inject learned binary/ternary nogood cavity repulsion into marginals
        for ng in &nogoods.nogood_clauses {
            if ng.len() < 2 {
                continue;
            }
            // Check if any literal is already satisfied (avoids the forbidden assignment)
            let mut already_avoided = false;
            for &(v, forb) in ng {
                if let Some(val) = fixed[v] {
                    if val != forb {
                        already_avoided = true;
                        break;
                    }
                }
            }
            if already_avoided {
                continue;
            }
            for (idx, &(v, forb)) in ng.iter().enumerate() {
                if fixed[v].is_some() {
                    continue;
                }
                // Product of forbidden probabilities of all other literals in this nogood
                let mut other_forb_prob = 1.0f64;
                for (j, &(u, u_forb)) in ng.iter().enumerate() {
                    if j == idx {
                        continue;
                    }
                    let pu = if u_forb == 1 { self.p1[u] } else { self.p0[u] };
                    other_forb_prob *= pu.max(0.05);
                }
                let penalty = (1.0 - 0.8 * other_forb_prob).clamp(0.15, 1.0);
                if forb == 1 {
                    self.p1[v] *= penalty;
                } else {
                    self.p0[v] *= penalty;
                }
                let z = (self.p0[v] + self.p1[v] + self.p_star[v]).max(eps);
                self.p0[v] /= z;
                self.p1[v] /= z;
                self.p_star[v] /= z;
            }
        }
        sweeps_done
    }

    /// Conflict-aware greedy rounding ordered by SP frozen 1-bias.
    pub fn greedy_round(&mut self, inc: &Incidence, fixed: &[Option<u8>]) -> &[u8] {
        self.cand.fill(0);
        self.clause_hits.fill(0);
        for i in 0..self.n {
            if fixed[i] == Some(1) {
                self.cand[i] = 1;
                for &(c_idx, mult) in inc.clauses_of(i) {
                    self.clause_hits[c_idx] = self.clause_hits[c_idx].saturating_add(mult);
                }
            }
        }

        let p1 = &self.p1;
        let p0 = &self.p0;
        self.order.sort_by(|&a, &b| {
            let sa = p1[a] - p0[a];
            let sb = p1[b] - p0[b];
            sb.partial_cmp(&sa)
                .unwrap_or(std::cmp::Ordering::Equal)
                .then_with(|| a.cmp(&b))
        });

        for &v in &self.order {
            if fixed[v].is_some() {
                continue;
            }
            let mut can_set = true;
            for &(c_idx, mult) in inc.clauses_of(v) {
                if mult > 1 || self.clause_hits[c_idx] > 0 {
                    can_set = false;
                    break;
                }
            }
            if can_set {
                self.cand[v] = 1;
                for &(c_idx, mult) in inc.clauses_of(v) {
                    self.clause_hits[c_idx] = self.clause_hits[c_idx].saturating_add(mult);
                }
            }
        }
        &self.cand
    }

    /// Select the single highest frozen-bias variable (high |P_i^1 - P_i^0|, low P_i^*),
    /// respecting nogood repulsion so previously failed short prefixes are avoided.
    pub fn pick_frozen_clamp(
        &self,
        active_vars: &[usize],
        inc: &Incidence,
        nogoods: &NogoodStore,
        current_clamps: &[(usize, u8)],
    ) -> Option<(usize, u8)> {
        let mut best: Option<(usize, u8, f64)> = None;

        for &v in active_vars {
            let p0 = self.p0[v];
            let p1 = self.p1[v];
            let ps = self.p_star[v];
            let polarization = (p1 - p0).abs();
            // Favor strongly frozen variables (low water P_i^*) and higher active degree
            let frozen_weight = (1.0 - 0.75 * ps).max(0.05);
            let deg_bonus = 1.0 + 0.25 * (inc.degrees[v] as f64).ln_1p();
            let mut pref_val = if p1 >= p0 { 1u8 } else { 0u8 };
            let mut score = (polarization + 1e-3) * frozen_weight * deg_bonus;

            if nogoods.would_repeat_failed(current_clamps, v, pref_val) {
                // Flip to opposite value if it does not also repeat a failed prefix
                let alt = pref_val ^ 1;
                if nogoods.would_repeat_failed(current_clamps, v, alt) {
                    score *= 0.01;
                } else {
                    pref_val = alt;
                    score *= 0.75;
                }
            }

            if best.map_or(true, |(_, _, bs)| score > bs) {
                best = Some((v, pref_val, score));
            }
        }

        best.map(|(v, val, _)| (v, val))
    }

    /// Bounded O(n) Cluster-Guided WalkSAT Island Polish (Layer 2.8).
    ///
    /// Triggered when SP decimation freezes >= 70% of variables without contradiction.
    /// Runs at most `max_flips = (8 * n).max(200)` focused min-conflicts flips strictly
    /// on unfrozen island variables to repair residual unsatisfied 1-in-3 clauses.
    pub fn walksat_island_polish(
        &mut self,
        inst: &Instance,
        inc: &Incidence,
        fixed: &[Option<u8>],
        seed: u64,
        ledger: &mut BitLedger,
    ) -> Option<Vec<u8>> {
        let n = self.n;
        let m = self.m;
        let mut assign = self.greedy_round(inc, fixed).to_vec();
        let mut hits = vec![0u8; m];
        let mut unsat_list: Vec<usize> = Vec::new();
        let mut unsat_pos = vec![usize::MAX; m];

        for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
            let h = assign[a] + assign[b] + assign[c];
            hits[c_idx] = h;
            if h != 1 {
                unsat_pos[c_idx] = unsat_list.len();
                unsat_list.push(c_idx);
            }
        }
        if unsat_list.is_empty() {
            return Some(assign);
        }

        let max_flips = (8 * n).max(200);
        let mut rng = 0x243f6a8885a308d3u64 ^ seed.wrapping_mul(0x9e3779b97f4a7c15);
        let mut next_u64 = || -> u64 {
            rng = rng.wrapping_add(0x9e3779b97f4a7c15);
            let mut z = rng;
            z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
            z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
            z ^ (z >> 31)
        };

        for _step in 0..max_flips {
            if unsat_list.is_empty() {
                return Some(assign);
            }
            let c_idx = unsat_list[(next_u64() as usize) % unsat_list.len()];
            let cl = inst.clauses[c_idx];

            let mut free_lits: [usize; 3] = [0; 3];
            let mut n_free = 0usize;
            for &v in &cl {
                if fixed[v].is_none() && !free_lits[..n_free].contains(&v) {
                    free_lits[n_free] = v;
                    n_free += 1;
                }
            }
            if n_free == 0 {
                return None;
            }

            // Pick best unfixed variable in this unsatisfied clause (or random with p = 0.25)
            let chosen = if (next_u64() & 3) == 0 {
                free_lits[(next_u64() as usize) % n_free]
            } else {
                let mut best_v = free_lits[0];
                let mut best_delta = i32::MAX;
                for &v in &free_lits[..n_free] {
                    let old_val = assign[v];
                    let mut delta = 0i32;
                    for &(ci, mult) in inc.clauses_of(v) {
                        let old_h = hits[ci];
                        let new_h = if old_val == 0 {
                            old_h.saturating_add(mult)
                        } else {
                            old_h.saturating_sub(mult)
                        };
                        let was_sat = old_h == 1;
                        let now_sat = new_h == 1;
                        if was_sat && !now_sat {
                            delta += 1;
                        } else if !was_sat && now_sat {
                            delta -= 1;
                        }
                    }
                    if delta < best_delta {
                        best_delta = delta;
                        best_v = v;
                    }
                }
                best_v
            };

            // Flip `chosen` and update `hits` + `unsat_list` in O(deg(chosen))
            let old_val = assign[chosen];
            assign[chosen] = old_val ^ 1;
            ledger.unit_prop_ops += 1;
            for &(ci, mult) in inc.clauses_of(chosen) {
                let old_h = hits[ci];
                let new_h = if old_val == 0 {
                    old_h.saturating_add(mult)
                } else {
                    old_h.saturating_sub(mult)
                };
                hits[ci] = new_h;
                let was_unsat = unsat_pos[ci] != usize::MAX;
                let now_unsat = new_h != 1;
                if was_unsat && !now_unsat {
                    let pos = unsat_pos[ci];
                    let last = unsat_list.pop().unwrap();
                    if pos < unsat_list.len() {
                        unsat_list[pos] = last;
                        unsat_pos[last] = pos;
                    }
                    unsat_pos[ci] = usize::MAX;
                } else if !was_unsat && now_unsat {
                    unsat_pos[ci] = unsat_list.len();
                    unsat_list.push(ci);
                }
            }
        }

        if unsat_list.is_empty() {
            Some(assign)
        } else {
            None
        }
    }
}
