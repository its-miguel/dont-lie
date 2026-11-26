//! Layer 2.75: Bounded Integer Cutting-Planes Engine (Z-Linear Refutation Dual).
//!
//! Combines:
//! 1. Exact Z-linear lifting of Monotone 1-in-3 clauses and verified root constants.
//! 2. Bounded degree-2 equality chain elimination over Z (collapsing carry/negation chains).
//! 3. Conflict-graph pairwise edge lifting + O(r^2) divisor-2 Gomory-Chvatal clique cuts.
//! 4. General bipartite Z-linear counting cancellation (detecting 0 <= -1 contradictions such as
//!    Pigeonhole Principle PHP_k^{k+1} and Hall-type counting barriers) with strict 32-bit
//!    coefficient safety (|A_i| <= 2^31 - 1, OVERFLOW = 0) and 100% proof-carrying traces.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::algebra::AlgebraicState;
use crate::instance::Instance;
use crate::ledger::BitLedger;
use crate::verifier::ProofStep;

const MAX_COEFF_ABS: i64 = (i32::MAX as i64) - 1;

#[derive(Clone, Debug)]
struct IntRow {
    lhs: BTreeMap<usize, i64>,
    rhs: i64,
}

#[derive(Clone, Debug)]
struct IntEquality {
    upper_id: usize,
    lower_id: usize,
    coeffs: BTreeMap<usize, i64>,
    active: bool,
}

struct CutEngine<'a> {
    rows: Vec<IntRow>,
    box_lo: Vec<Option<usize>>, // -x_v <= 0
    box_hi: Vec<Option<usize>>, // x_v <= 1
    alg: &'a mut AlgebraicState,
    ledger: &'a mut BitLedger,
}

impl<'a> CutEngine<'a> {
    fn new(n: usize, alg: &'a mut AlgebraicState, ledger: &'a mut BitLedger) -> Self {
        Self {
            rows: Vec::new(),
            box_lo: vec![None; n],
            box_hi: vec![None; n],
            alg,
            ledger,
        }
    }

    fn emit_step(&mut self, step: ProofStep) {
        if self.alg.record_proof {
            self.alg.proof_steps.push(step);
        }
    }

    fn lift_clause(&mut self, inst: &Instance, c_idx: usize, is_upper: bool) -> usize {
        let [a, b, c] = inst.clauses[c_idx];
        let sign: i64 = if is_upper { 1 } else { -1 };
        let mut lhs: BTreeMap<usize, i64> = BTreeMap::new();
        *lhs.entry(a).or_insert(0) += sign;
        *lhs.entry(b).or_insert(0) += sign;
        *lhs.entry(c).or_insert(0) += sign;
        lhs.retain(|_, v| *v != 0);
        for &v in lhs.values() {
            self.ledger.record_int(v);
        }
        self.ledger.record_int(sign);
        self.emit_step(ProofStep::IntegerClauseLift { c_idx, is_upper });
        let id = self.rows.len();
        self.rows.push(IntRow { lhs, rhs: sign });
        id
    }

    fn get_box_lo(&mut self, v: usize) -> usize {
        if let Some(id) = self.box_lo[v] {
            return id;
        }
        self.emit_step(ProofStep::IntegerBoxBound { v, is_upper: false });
        let mut lhs = BTreeMap::new();
        lhs.insert(v, -1);
        let id = self.rows.len();
        self.rows.push(IntRow { lhs, rhs: 0 });
        self.box_lo[v] = Some(id);
        id
    }

    fn get_box_hi(&mut self, v: usize) -> usize {
        if let Some(id) = self.box_hi[v] {
            return id;
        }
        self.emit_step(ProofStep::IntegerBoxBound { v, is_upper: true });
        let mut lhs = BTreeMap::new();
        lhs.insert(v, 1);
        let id = self.rows.len();
        self.rows.push(IntRow { lhs, rhs: 1 });
        self.box_hi[v] = Some(id);
        id
    }

    fn lift_const(&mut self, v: usize, val: u8, const_id: usize, is_upper: bool) -> usize {
        self.emit_step(ProofStep::IntegerConstLift {
            const_id,
            v,
            val,
            is_upper,
        });
        let iv = val as i64;
        let mut lhs = BTreeMap::new();
        let rhs = if is_upper {
            lhs.insert(v, 1);
            iv
        } else {
            lhs.insert(v, -1);
            -iv
        };
        let id = self.rows.len();
        self.rows.push(IntRow { lhs, rhs });
        id
    }

    /// Apply a Gomory-Chvatal cut with strict 32-bit coefficient safety.
    /// Returns `Some(new_row_id)` if exact divisibility & 32-bit bounds hold, else `None`.
    fn apply_cut(
        &mut self,
        parent_rows: Vec<usize>,
        multipliers: Vec<i64>,
        divisor: i64,
    ) -> Option<usize> {
        if divisor < 1 || parent_rows.is_empty() || parent_rows.len() != multipliers.len() {
            return None;
        }
        let mut combined: BTreeMap<usize, i128> = BTreeMap::new();
        let mut rhs_sum: i128 = 0;

        for (&rid, &mult) in parent_rows.iter().zip(multipliers.iter()) {
            if mult < 0 {
                return None;
            }
            if mult == 0 {
                continue;
            }
            let m128 = mult as i128;
            let row = &self.rows[rid];
            for (&v, &c) in &row.lhs {
                *combined.entry(v).or_insert(0) += m128 * (c as i128);
            }
            rhs_sum += m128 * (row.rhs as i128);
        }

        let d128 = divisor as i128;
        let mut new_lhs: BTreeMap<usize, i64> = BTreeMap::new();
        let mut lhs_vec: Vec<(usize, i64)> = Vec::new();
        for (v, coeff) in combined {
            if coeff == 0 {
                continue;
            }
            if coeff % d128 != 0 {
                return None;
            }
            let q = coeff / d128;
            if q.abs() > (MAX_COEFF_ABS as i128) {
                // Strict 32-bit bit-width guardrail: drop candidate cut cleanly
                return None;
            }
            let qi = q as i64;
            self.ledger.record_int(qi);
            new_lhs.insert(v, qi);
            lhs_vec.push((v, qi));
        }

        let rhs_div = rhs_sum.div_euclid(d128);
        if rhs_div.abs() > (MAX_COEFF_ABS as i128) {
            return None;
        }
        let new_rhs = rhs_div as i64;
        self.ledger.record_int(new_rhs);
        self.ledger.s_poly_reductions += 1;

        self.emit_step(ProofStep::IntegerCut {
            parent_rows,
            multipliers,
            divisor,
            lhs: lhs_vec,
            rhs: new_rhs,
        });
        let id = self.rows.len();
        self.rows.push(IntRow {
            lhs: new_lhs,
            rhs: new_rhs,
        });
        Some(id)
    }

    fn emit_contradiction(&mut self, row_id: usize) {
        self.emit_step(ProofStep::IntegerContradiction { row_id });
        self.alg.inconsistent = true;
    }

    fn lift_equiv(&mut self, eq_id: usize, u: usize, v: usize, u_minus_v: bool) -> usize {
        self.emit_step(ProofStep::IntegerEquivLift {
            eq_id,
            u,
            v,
            u_minus_v,
        });
        let mut lhs = BTreeMap::new();
        if u_minus_v {
            lhs.insert(u, 1);
            lhs.insert(v, -1);
        } else {
            lhs.insert(v, 1);
            lhs.insert(u, -1);
        }
        self.ledger.record_int(1);
        let id = self.rows.len();
        self.rows.push(IntRow { lhs, rhs: 0 });
        id
    }
}

/// Run bounded Gomory-Chvatal integer cutting-planes closure at the root.
/// Returns `Ok(forced_unit_bounds)` if consistent, or `Err(())` if `0 <= -1` contradiction derived.
pub fn run_cutting_planes_dual(
    inst: &Instance,
    alg: &mut AlgebraicState,
    ledger: &mut BitLedger,
) -> Result<Vec<(usize, u8)>, ()> {
    let n = inst.n_vars;
    let m = inst.m_clauses();
    if m == 0 || alg.inconsistent {
        return if alg.inconsistent { Err(()) } else { Ok(Vec::new()) };
    }

    let mut eng = CutEngine::new(n, alg, ledger);

    // 1. Lift known root constants into Z bounds
    let mut const_hi: Vec<Option<usize>> = vec![None; n];
    let mut const_lo: Vec<Option<usize>> = vec![None; n];
    for v in 0..n {
        if let Some(val) = eng.alg.fixed[v] {
            if let Some(cid) = eng.alg.const_lemma_id[v] {
                const_hi[v] = Some(eng.lift_const(v, val, cid, true));
                const_lo[v] = Some(eng.lift_const(v, val, cid, false));
            }
        }
    }

    // 1b. Complete Cross-lens F_2 -> Z bridge: extract ALL verified binary equivalences (x_u ^ x_v = 0)
    //     implied by RREF:
    //     (i)  direct 2-bit rhs==0 rows (pcol ^ free = 0), and
    //     (ii) ANY two pivot rows sharing the exact same (free_tail, rhs) signature
    //          (p1 ^ tail = r, p2 ^ tail = r  ==>  F2Xor gives verified p1 ^ p2 = 0!).
    let mut equiv_pairs: Vec<(usize, usize, usize)> = Vec::new(); // (u, target_v, eq_id)
    let mut tail_buckets: HashMap<(Vec<u64>, u8), Vec<(usize, usize)>> = HashMap::new();
    for &pcol in &eng.alg.pivot_cols {
        if eng.alg.fixed[pcol].is_some() {
            continue;
        }
        if let Some(prow) = eng.alg.pivots[pcol].as_ref() {
            let mut tail = prow.words.clone();
            tail[pcol >> 6] ^= 1u64 << (pcol & 63);
            let tail_pop: u32 = tail.iter().map(|w| w.count_ones()).sum();
            if tail_pop == 0 {
                continue;
            }
            if tail_pop == 1 && prow.rhs == 0 {
                // Direct pcol ^ free = 0
                let mut ov = usize::MAX;
                for (wi, &w) in tail.iter().enumerate() {
                    if w != 0 {
                        ov = (wi << 6) + (w.trailing_zeros() as usize);
                        break;
                    }
                }
                if ov != usize::MAX && eng.alg.fixed[ov].is_none() {
                    equiv_pairs.push((pcol, ov, prow.lemma_id));
                }
            } else {
                tail_buckets
                    .entry((tail, prow.rhs))
                    .or_default()
                    .push((pcol, prow.lemma_id));
            }
        }
    }
    let mut tail_keys: Vec<(Vec<u64>, u8)> = tail_buckets.keys().cloned().collect();
    tail_keys.sort();
    for tk in tail_keys {
        let group = &tail_buckets[&tk];
        if group.len() >= 2 {
            let (rep_p, rep_lid) = group[0];
            for &(pk, lid_k) in &group[1..] {
                let new_lid = if eng.alg.record_proof {
                    eng.alg.proof_steps.push(ProofStep::F2Xor {
                        lhs: rep_lid,
                        rhs: lid_k,
                    });
                    let id = eng.alg.next_lemma_id;
                    eng.alg.next_lemma_id += 1;
                    id
                } else {
                    0
                };
                equiv_pairs.push((pk, rep_p, new_lid));
            }
        }
    }
    // equiv_map[u] = Some((target_v, row_u_minus_v, row_v_minus_u))
    let mut equiv_map: Vec<Option<(usize, usize, usize)>> = vec![None; n];
    for &(u, v, eq_id) in &equiv_pairs {
        let r_uv = eng.lift_equiv(eq_id, u, v, true);
        let r_vu = eng.lift_equiv(eq_id, u, v, false);
        equiv_map[u] = Some((v, r_uv, r_vu));
    }

    // 2. Lift all raw clauses into Z equalities (upper & lower rows) and substitute root constants & F_2 equivalences
    let mut eqs: Vec<IntEquality> = Vec::with_capacity(m);
    let mut seen_eqs: HashSet<(Vec<(usize, i64)>, i64)> = HashSet::with_capacity(m * 2);
    let mut conflict_edge_row: HashMap<(usize, usize), usize> = HashMap::new();
    let mut conflict_adj: Vec<HashSet<usize>> = vec![HashSet::new(); n];

    for c_idx in 0..m {
        let [a, b, c] = inst.clauses[c_idx];
        let mut up = eng.lift_clause(inst, c_idx, true);
        let mut lo = eng.lift_clause(inst, c_idx, false);

        // Derive pairwise conflict edges (x_u + x_v <= 1) canonicalized through F_2 equivalences
        if a != b && a != c && b != c {
            let pairs = [(a, b, c), (a, c, b), (b, c, a)];
            for (u, v, w) in pairs {
                if eng.alg.fixed[u].is_none() && eng.alg.fixed[v].is_none() {
                    let cu = equiv_map[u].map_or(u, |(t, _, _)| t);
                    let cv = equiv_map[v].map_or(v, |(t, _, _)| t);
                    if cu == cv {
                        continue;
                    }
                    let key = if cu < cv { (cu, cv) } else { (cv, cu) };
                    if !conflict_edge_row.contains_key(&key) {
                        let box_w = eng.get_box_lo(w);
                        let mut pr = vec![up, box_w];
                        let mut pm = vec![1i64, 1i64];
                        if let Some((_, _, r_vu)) = equiv_map[u] {
                            pr.push(r_vu);
                            pm.push(1);
                        }
                        if let Some((_, _, r_vu)) = equiv_map[v] {
                            pr.push(r_vu);
                            pm.push(1);
                        }
                        if let Some(erow) = eng.apply_cut(pr, pm, 1) {
                            conflict_edge_row.insert(key, erow);
                            conflict_adj[key.0].insert(key.1);
                            conflict_adj[key.1].insert(key.0);
                        }
                    }
                }
            }
        }

        // Substitute any known root constants and F_2 binary equivalences out of (up, lo)
        let mut p_up = vec![up];
        let mut m_up = vec![1i64];
        let mut p_lo = vec![lo];
        let mut m_lo = vec![1i64];
        let row_terms: Vec<(usize, i64)> = eng.rows[up].lhs.iter().map(|(&k, &v)| (k, v)).collect();
        let mut needs_subst = false;
        for (v, coeff) in row_terms {
            if let (Some(clo), Some(chi)) = (const_lo[v], const_hi[v]) {
                needs_subst = true;
                // In up: +coeff * x_v; add coeff * (-x_v <= -val) to eliminate x_v
                p_up.push(clo);
                m_up.push(coeff);
                // In lo: -coeff * x_v; add coeff * (+x_v <= +val) to eliminate x_v
                p_lo.push(chi);
                m_lo.push(coeff);
            } else if let Some((_, r_uv, r_vu)) = equiv_map[v] {
                needs_subst = true;
                // In up: +coeff * x_v; add coeff * (x_target - x_v <= 0)
                p_up.push(r_vu);
                m_up.push(coeff);
                // In lo: -coeff * x_v; add coeff * (x_v - x_target <= 0)
                p_lo.push(r_uv);
                m_lo.push(coeff);
            }
        }
        if needs_subst {
            if let (Some(u2), Some(l2)) = (
                eng.apply_cut(p_up, m_up, 1),
                eng.apply_cut(p_lo, m_lo, 1),
            ) {
                up = u2;
                lo = l2;
            }
        }

        if eng.rows[up].lhs.is_empty() && eng.rows[up].rhs < 0 {
            eng.emit_contradiction(up);
            return Err(());
        }
        if eng.rows[lo].lhs.is_empty() && eng.rows[lo].rhs < 0 {
            eng.emit_contradiction(lo);
            return Err(());
        }

        let coeffs = eng.rows[up].lhs.clone();
        if !coeffs.is_empty() {
            let eq_key: (Vec<(usize, i64)>, i64) = (
                coeffs.iter().map(|(&k, &v)| (k, v)).collect(),
                eng.rows[up].rhs,
            );
            if seen_eqs.insert(eq_key) {
                eqs.push(IntEquality {
                    upper_id: up,
                    lower_id: lo,
                    coeffs,
                    active: true,
                });
            }
        }
    }

    // 3. Bounded Z-Linear Equality Chain Elimination (eliminates degree-2 chain variables)
    //    E.g. collapses carry chains `p0 + p1 + neg_c1 = 1`, `neg_c1 + c1 = 1`, ... into sum(p) = 1!
    let max_elim_passes = n;
    for _pass in 0..max_elim_passes {
        // Count how many active equalities each variable appears in
        let mut var_eqs: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (ei, eq) in eqs.iter().enumerate() {
            if !eq.active {
                continue;
            }
            for &v in eq.coeffs.keys() {
                var_eqs[v].push(ei);
            }
        }

        let mut eliminated_any = false;
        for v in 0..n {
            if var_eqs[v].len() != 2 {
                continue;
            }
            let e1 = var_eqs[v][0];
            let e2 = var_eqs[v][1];
            if !eqs[e1].active || !eqs[e2].active {
                continue;
            }
            let c1 = *eqs[e1].coeffs.get(&v).unwrap_or(&0);
            let c2 = *eqs[e2].coeffs.get(&v).unwrap_or(&0);
            if c1.abs() != 1 || c2.abs() != 1 {
                continue;
            }
            if eqs[e1].coeffs.len() + eqs[e2].coeffs.len() > 64 {
                continue;
            }
            // Never eliminate a core variable `v` into a dead-end degree-1 variable
            // (e.g. substituting a clique variable p out via a redundant `c1 + p = 1` where c1 has degree 1).
            if eqs[e1].coeffs.keys().any(|&u| u != v && var_eqs[u].len() == 1)
                || eqs[e2].coeffs.keys().any(|&u| u != v && var_eqs[u].len() == 1)
            {
                continue;
            }

            // Combine e1 and e2 so v cancels cleanly:
            // If c1 == c2 (same sign): up_new = up(e2) + lo(e1), lo_new = lo(e2) + up(e1)
            // If c1 == -c2 (opposite sign): up_new = up(e2) + up(e1), lo_new = lo(e2) + lo(e1)
            let (p_up, p_lo) = if c1 == c2 {
                (
                    vec![eqs[e2].upper_id, eqs[e1].lower_id],
                    vec![eqs[e2].lower_id, eqs[e1].upper_id],
                )
            } else {
                (
                    vec![eqs[e2].upper_id, eqs[e1].upper_id],
                    vec![eqs[e2].lower_id, eqs[e1].lower_id],
                )
            };

            if let (Some(new_up), Some(new_lo)) = (
                eng.apply_cut(p_up, vec![1, 1], 1),
                eng.apply_cut(p_lo, vec![1, 1], 1),
            ) {
                if eng.rows[new_up].lhs.is_empty() && eng.rows[new_up].rhs < 0 {
                    eng.emit_contradiction(new_up);
                    return Err(());
                }
                if eng.rows[new_lo].lhs.is_empty() && eng.rows[new_lo].rhs < 0 {
                    eng.emit_contradiction(new_lo);
                    return Err(());
                }
                let new_coeffs = eng.rows[new_up].lhs.clone();
                eqs[e1].active = false;
                eqs[e2].active = false;
                if !new_coeffs.is_empty() {
                    eqs.push(IntEquality {
                        upper_id: new_up,
                        lower_id: new_lo,
                        coeffs: new_coeffs,
                        active: true,
                    });
                }
                eliminated_any = true;
                break; // refresh var_eqs on next pass
            }
        }
        if !eliminated_any {
            break;
        }
    }

    // 4. Conflict-Graph Maximal Cliques -> Proof-Carrying Divisor-2 Gomory-Chvatal Clique Cuts
    //    For every non-trivial clique C (size >= 4, or size == 3 not identical to a single raw clause),
    //    derives sum_{v in C} x_v <= 1 in O(r^2) d=2 cuts!
    let mut raw_3clauses: HashSet<[usize; 3]> = HashSet::with_capacity(m * 2);
    for &[a, b, c] in &inst.clauses {
        let mut key = [
            equiv_map[a].map_or(a, |(t, _, _)| t),
            equiv_map[b].map_or(b, |(t, _, _)| t),
            equiv_map[c].map_or(c, |(t, _, _)| t),
        ];
        key.sort_unstable();
        raw_3clauses.insert(key);
    }

    let mut clique_rows: Vec<(Vec<usize>, usize)> = Vec::new();
    let mut seen_cliques: HashSet<Vec<usize>> = HashSet::new();

    // Sort candidate seed vertices by conflict degree descending
    let mut seeds: Vec<usize> = (0..n).filter(|&v| conflict_adj[v].len() >= 2).collect();
    seeds.sort_by(|&a, &b| conflict_adj[b].len().cmp(&conflict_adj[a].len()).then_with(|| a.cmp(&b)));

    // Phase 4a: Collect all candidate maximal cliques without premature covered_in_clique blocking
    let mut cand_cliques: Vec<Vec<usize>> = Vec::new();
    for &seed in &seeds {
        let mut clique = vec![seed];
        let mut cands: Vec<(usize, usize)> = conflict_adj[seed]
            .iter()
            .copied()
            .map(|u| {
                let common = conflict_adj[u]
                    .iter()
                    .filter(|&&w| conflict_adj[seed].contains(&w))
                    .count();
                (u, common)
            })
            .collect();
        cands.sort_by(|&(ua, ca), &(ub, cb)| {
            cb.cmp(&ca)
                .then_with(|| conflict_adj[ub].len().cmp(&conflict_adj[ua].len()))
                .then_with(|| ua.cmp(&ub))
        });
        for (u, _) in cands {
            if clique.iter().all(|&w| conflict_adj[u].contains(&w)) {
                clique.push(u);
            }
        }
        if clique.len() < 3 {
            continue;
        }
        clique.sort_unstable();
        if clique.len() == 3 && raw_3clauses.contains(&[clique[0], clique[1], clique[2]]) {
            continue;
        }
        if seen_cliques.insert(clique.clone()) {
            cand_cliques.push(clique);
        }
    }
    // Sort candidate cliques strictly by size DESCENDING so true counting cliques (size k+1)
    // always take precedence over smaller 3-triangles!
    cand_cliques.sort_by(|a, b| b.len().cmp(&a.len()).then_with(|| a.cmp(b)));

    let mut covered_in_clique = vec![false; n];
    for clique in cand_cliques {
        if clique.iter().any(|&v| covered_in_clique[v]) {
            continue;
        }

        // Derive sum_{v in clique} x_v <= 1 using ONLY divisor-2 Gomory-Chvatal cuts!
        let r = clique.len();
        let mut s_rows: Vec<usize> = Vec::with_capacity(r);
        s_rows.push(0); // unused slot 0
        let mut ok = true;
        for k in 1..r {
            let key = (clique[0], clique[k]);
            if let Some(&erow) = conflict_edge_row.get(&key) {
                s_rows.push(erow);
            } else {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        // Inductive step t = 2..r-1:
        // S_{t+1}(k) = cut([S_t(t-1), S_t(k), edge(v_{t-1}, v_k)], [1, 1, 1], divisor=2)
        for t in 2..r {
            let prev_row = s_rows[t - 1];
            let mut next_s = s_rows.clone();
            for k in t..r {
                let key = (clique[t - 1], clique[k]);
                let Some(&erow) = conflict_edge_row.get(&key) else {
                    ok = false;
                    break;
                };
                let Some(cut_row) = eng.apply_cut(vec![prev_row, s_rows[k], erow], vec![1, 1, 1], 2)
                else {
                    ok = false;
                    break;
                };
                next_s[k] = cut_row;
            }
            if !ok {
                break;
            }
            s_rows = next_s;
        }
        if ok {
            let final_clique_row = s_rows[r - 1];
            for &v in &clique {
                covered_in_clique[v] = true;
            }
            clique_rows.push((clique, final_clique_row));
        }
    }

    // 5. General Global Counting Cancellation (Upper-Bound Cliques vs. Lower-Bound Sums)
    //    Identify active lower-bound rows (-sum_{v in T} x_v <= -c, all coeffs == -1, rhs <= -1)
    //    and check if a connected component of lower bounds + covering cliques sums to 0 <= -1!
    let mut lower_bounds: Vec<(Vec<usize>, usize, i64)> = Vec::new();
    for eq in &eqs {
        if !eq.active {
            continue;
        }
        // Check BOTH orientations (lower_id and upper_id) of the exact equality for a
        // negative-only lower bound (-sum_{v in T} x_v <= -c) whose support is clique-covered.
        for &rid in &[eq.lower_id, eq.upper_id] {
            let lrow = &eng.rows[rid];
            if lrow.rhs <= -1
                && lrow.lhs.values().all(|&c| c == -1)
                && lrow.lhs.keys().all(|&v| covered_in_clique[v])
            {
                let vars: Vec<usize> = lrow.lhs.keys().copied().collect();
                lower_bounds.push((vars, rid, -lrow.rhs));
            }
        }
    }

    if !clique_rows.is_empty() && !lower_bounds.is_empty() {
        // Map each variable to the clique(s) covering it
        let mut var_to_cliques: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (ci, (vars, _)) in clique_rows.iter().enumerate() {
            for &v in vars {
                var_to_cliques[v].push(ci);
            }
        }
        // Map each variable to lower-bound rows containing it
        let mut var_to_lbs: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (li, (vars, _, _)) in lower_bounds.iter().enumerate() {
            for &v in vars {
                var_to_lbs[v].push(li);
            }
        }

        // BFS connected components in the bipartite (lower_bounds <-> clique_rows) graph
        let mut visited_lb = vec![false; lower_bounds.len()];
        let mut visited_clq = vec![false; clique_rows.len()];

        for start_lb in 0..lower_bounds.len() {
            if visited_lb[start_lb] {
                continue;
            }
            let mut comp_lbs = Vec::new();
            let mut comp_clqs = Vec::new();
            let mut q_lb = vec![start_lb];
            visited_lb[start_lb] = true;

            while let Some(li) = q_lb.pop() {
                comp_lbs.push(li);
                for &v in &lower_bounds[li].0 {
                    for &ci in &var_to_cliques[v] {
                        if !visited_clq[ci] {
                            visited_clq[ci] = true;
                            comp_clqs.push(ci);
                            for &u in &clique_rows[ci].0 {
                                for &li2 in &var_to_lbs[u] {
                                    if !visited_lb[li2] {
                                        visited_lb[li2] = true;
                                        q_lb.push(li2);
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if comp_clqs.is_empty() {
                continue;
            }

            // Compute net balance when summing all cliques + all lower bounds in this component
            let mut net: BTreeMap<usize, i64> = BTreeMap::new();
            let mut parent_rows: Vec<usize> = Vec::with_capacity(comp_clqs.len() + comp_lbs.len());
            let mut multipliers: Vec<i64> = Vec::with_capacity(comp_clqs.len() + comp_lbs.len());
            let mut rhs_balance: i64 = 0;

            for &ci in &comp_clqs {
                let rid = clique_rows[ci].1;
                parent_rows.push(rid);
                multipliers.push(1);
                for (&v, &c) in &eng.rows[rid].lhs {
                    *net.entry(v).or_insert(0) += c;
                }
                rhs_balance += eng.rows[rid].rhs;
            }
            for &li in &comp_lbs {
                let rid = lower_bounds[li].1;
                parent_rows.push(rid);
                multipliers.push(1);
                for (&v, &c) in &eng.rows[rid].lhs {
                    *net.entry(v).or_insert(0) += c;
                }
                rhs_balance += eng.rows[rid].rhs;
            }

            // Cancel residual positive coeffs via box_lo (-x_v <= 0, adds 0 to RHS)
            // and residual negative coeffs via box_hi (+x_v <= 1, adds +|c| to RHS)
            let mut extra_rhs = 0i64;
            for &c in net.values() {
                if c < 0 {
                    extra_rhs += -c;
                }
            }
            if rhs_balance + extra_rhs <= -1 {
                for (&v, &c) in &net {
                    if c > 0 {
                        let blo = eng.get_box_lo(v);
                        parent_rows.push(blo);
                        multipliers.push(c);
                    } else if c < 0 {
                        let bhi = eng.get_box_hi(v);
                        parent_rows.push(bhi);
                        multipliers.push(-c);
                    }
                }
                if let Some(final_row) = eng.apply_cut(parent_rows, multipliers, 1) {
                    if eng.rows[final_row].lhs.is_empty() && eng.rows[final_row].rhs <= -1 {
                        eng.emit_contradiction(final_row);
                        return Err(());
                    }
                }
            }
        }
    }

    // 6. Extract any newly derived single-variable integer unit bounds (x_v <= 0 or -x_v <= -1)
    let mut forced: Vec<(usize, u8)> = Vec::new();
    for row in &eng.rows {
        if row.lhs.len() == 1 {
            let (&v, &c) = row.lhs.iter().next().unwrap();
            if eng.alg.fixed[v].is_some() {
                continue;
            }
            if c > 0 && row.rhs <= 0 {
                forced.push((v, 0));
            } else if c < 0 && row.rhs <= c {
                forced.push((v, 1));
            }
        }
    }
    forced.sort_unstable();
    forced.dedup();
    Ok(forced)
}
