//! Upgrade 1 (Layer 2.5): Local Gadget Elimination (Peeling Low-Degree Auxiliary Variables).
//!
//! Detects connected clusters of low-degree auxiliary variables (deg <= 2 in non-negation clauses,
//! typical of Schaefer 3-OR / 3-SAT reduction gadgets), projects their exact truth-table relations
//! onto canonical core boundary variables (|core| <= 4), intersects truth tables sharing the same
//! core boundary, and injects all entailed F_2 affine equations directly into Phase 1's F_2 RREF
//! with independently verifiable `ProofStep::LocalClusterF2Axiom` traces.

use std::collections::{BTreeMap, HashMap, HashSet};

use crate::algebra::AlgebraicState;
use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;
use crate::verifier::ProofStep;

#[derive(Clone, Debug)]
struct ProjectedSubcluster {
    clause_ids: Vec<usize>,
    aux_vars: Vec<usize>,
    const_refs: Vec<(usize, u8, usize)>,
    /// Bitmask over 0..(1 << core_vars.len()) of satisfying core assignments.
    allowed_mask: u16,
}

/// Peel low-degree auxiliary variable clusters, intersect truth tables on identical core
/// variable tuples, and inject all entailed F_2 affine equations into `alg`.
/// Returns `(consistent, num_injected_eqs)`.
pub fn peel_gadgets_and_inject_f2(
    inst: &Instance,
    inc: &Incidence,
    alg: &mut AlgebraicState,
    ledger: &mut BitLedger,
) -> (bool, usize) {
    let n = inst.n_vars;
    let m = inst.m_clauses();

    // 1. Identify binary negation chains (u, v, c0) where fixed[c0] == Some(0).
    //    Build connected components so every variable in a negation chain (e.g. neg_q <-> q <-> c1 <-> neg_c1)
    //    canonicalizes to the same smallest-index root with its exact tree path of negation clauses.
    let mut neg_adj: Vec<Vec<(usize, usize, usize)>> = vec![Vec::new(); n];
    let mut in_neg_chain = vec![false; n];
    let mut is_neg_clause = vec![false; m];
    for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
        let lits = [a, b, c];
        let mut z_var = None;
        let mut others = Vec::with_capacity(2);
        for &v in &lits {
            if alg.fixed[v] == Some(0) && z_var.is_none() {
                z_var = Some(v);
            } else {
                others.push(v);
            }
        }
        if let Some(c0) = z_var {
            if others.len() == 2 && others[0] != others[1] {
                let (u, v) = (others[0], others[1]);
                if alg.fixed[u].is_none() && alg.fixed[v].is_none() {
                    is_neg_clause[c_idx] = true;
                    in_neg_chain[u] = true;
                    in_neg_chain[v] = true;
                    neg_adj[u].push((v, c_idx, c0));
                    neg_adj[v].push((u, c_idx, c0));
                }
            }
        }
    }

    // BFS each negation component from its smallest-index vertex `root`
    let mut neg_root: Vec<usize> = (0..n).collect();
    let mut neg_parent: Vec<Option<(usize, usize, usize)>> = vec![None; n]; // v -> (parent, c_idx, c0)
    let mut neg_vis = vec![false; n];
    for start in 0..n {
        if neg_vis[start] || neg_adj[start].is_empty() {
            continue;
        }
        let mut q = std::collections::VecDeque::new();
        neg_vis[start] = true;
        neg_root[start] = start;
        q.push_back(start);
        while let Some(u) = q.pop_front() {
            for &(v, c_idx, c0) in &neg_adj[u] {
                if !neg_vis[v] {
                    neg_vis[v] = true;
                    neg_root[v] = start;
                    neg_parent[v] = Some((u, c_idx, c0));
                    q.push_back(v);
                }
            }
        }
    }

    // 2. Count degree of each unfixed variable in non-negation clauses.
    //    Variables with deg in {1, 2} (and not part of a negation chain) are candidate auxiliaries!
    let mut non_neg_deg = vec![0usize; n];
    let mut non_neg_clauses: Vec<Vec<usize>> = vec![Vec::new(); n];
    for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
        if is_neg_clause[c_idx] {
            continue;
        }
        let mut uniq = [a, b, c];
        uniq.sort_unstable();
        for idx in 0..3 {
            if idx == 0 || uniq[idx] != uniq[idx - 1] {
                let v = uniq[idx];
                non_neg_deg[v] += 1;
                non_neg_clauses[v].push(c_idx);
            }
        }
    }

    let is_aux_cand = |v: usize| -> bool {
        alg.fixed[v].is_none()
            && !in_neg_chain[v]
            && non_neg_deg[v] >= 1
            && non_neg_deg[v] <= 2
    };

    // 3. Connected components of auxiliary candidates via shared non-negation clauses.
    let mut visited = vec![false; n];
    let mut groups: BTreeMap<Vec<usize>, Vec<ProjectedSubcluster>> = BTreeMap::new();

    for start in 0..n {
        if visited[start] || !is_aux_cand(start) {
            continue;
        }
        // BFS over auxiliary candidates connected by non-negation clauses
        let mut stack = vec![start];
        visited[start] = true;
        let mut aux_set: Vec<usize> = Vec::new();
        let mut clause_set: HashSet<usize> = HashSet::new();

        while let Some(u) = stack.pop() {
            aux_set.push(u);
            for &c_idx in &non_neg_clauses[u] {
                clause_set.insert(c_idx);
                for &lit in &inst.clauses[c_idx] {
                    if !visited[lit] && is_aux_cand(lit) {
                        visited[lit] = true;
                        stack.push(lit);
                    }
                }
            }
        }

        // Only project compact local gadgets (|aux| <= 4 so with <= 2 neg vars total <= 6)
        if aux_set.is_empty() || aux_set.len() > 4 || clause_set.len() > 8 {
            continue;
        }

        let aux_hash: HashSet<usize> = aux_set.iter().copied().collect();
        let mut core_set: HashSet<usize> = HashSet::new();
        let mut extra_aux: Vec<usize> = Vec::new();
        let mut extra_clauses: Vec<usize> = Vec::new();
        let mut const_refs_map: HashMap<usize, (u8, usize)> = HashMap::new();

        for &c_idx in &clause_set {
            for &lit in &inst.clauses[c_idx] {
                if aux_hash.contains(&lit) {
                    continue;
                }
                if let Some(val) = alg.fixed[lit] {
                    let lid = alg.const_lemma_id[lit].unwrap_or(0);
                    const_refs_map.insert(lit, (val, lid));
                } else {
                    let canon = neg_root[lit];
                    core_set.insert(canon);
                    let mut cur = lit;
                    while let Some((parent, neg_cidx, c0)) = neg_parent[cur] {
                        if !extra_aux.contains(&cur) {
                            extra_aux.push(cur);
                        }
                        if !extra_clauses.contains(&neg_cidx) {
                            extra_clauses.push(neg_cidx);
                        }
                        let c0_lid = alg.const_lemma_id[c0].unwrap_or(0);
                        const_refs_map.insert(c0, (0, c0_lid));
                        cur = parent;
                    }
                }
            }
        }

        let mut core_vars: Vec<usize> = core_set.into_iter().collect();
        core_vars.sort_unstable();
        if core_vars.is_empty() || core_vars.len() > 4 {
            continue;
        }

        let mut all_aux = aux_set;
        all_aux.extend(extra_aux);
        all_aux.sort_unstable();
        all_aux.dedup();
        if all_aux.len() > 8 {
            continue;
        }

        let mut all_clauses: Vec<usize> = clause_set.into_iter().collect();
        all_clauses.extend(extra_clauses);
        all_clauses.sort_unstable();
        all_clauses.dedup();

        let const_refs: Vec<(usize, u8, usize)> = const_refs_map
            .into_iter()
            .map(|(v, (val, lid))| (v, val, lid))
            .collect();

        // 4. Compute exact projected truth table over 2^|core_vars| assignments
        let n_core = core_vars.len();
        let n_aux = all_aux.len();
        let mut allowed_mask: u16 = 0;

        // Build compact local variable indexing for fast inner loop
        let mut local_idx: HashMap<usize, usize> = HashMap::new();
        for (i, &v) in core_vars.iter().enumerate() {
            local_idx.insert(v, i);
        }
        for (i, &v) in all_aux.iter().enumerate() {
            local_idx.insert(v, n_core + i);
        }
        let mut local_vals = vec![2u8; n_core + n_aux + const_refs.len()];
        for (i, &(v, val, _)) in const_refs.iter().enumerate() {
            local_idx.insert(v, n_core + n_aux + i);
            local_vals[n_core + n_aux + i] = val;
        }

        let mut local_clauses: Vec<[usize; 3]> = Vec::with_capacity(all_clauses.len());
        let mut mapping_ok = true;
        for &cid in &all_clauses {
            let [a, b, c] = inst.clauses[cid];
            if let (Some(&la), Some(&lb), Some(&lc)) =
                (local_idx.get(&a), local_idx.get(&b), local_idx.get(&c))
            {
                local_clauses.push([la, lb, lc]);
            } else {
                mapping_ok = false;
                break;
            }
        }
        if !mapping_ok {
            continue;
        }

        for cmask in 0u32..(1u32 << n_core) {
            for ci in 0..n_core {
                local_vals[ci] = ((cmask >> ci) & 1) as u8;
            }
            let mut sat = false;
            for amask in 0u32..(1u32 << n_aux) {
                for ai in 0..n_aux {
                    local_vals[n_core + ai] = ((amask >> ai) & 1) as u8;
                }
                let mut ok = true;
                for &[la, lb, lc] in &local_clauses {
                    if local_vals[la] + local_vals[lb] + local_vals[lc] != 1 {
                        ok = false;
                        break;
                    }
                }
                if ok {
                    sat = true;
                    break;
                }
            }
            if sat {
                allowed_mask |= 1u16 << cmask;
            }
            ledger.s_poly_reductions += 1;
        }

        groups
            .entry(core_vars)
            .or_default()
            .push(ProjectedSubcluster {
                clause_ids: all_clauses,
                aux_vars: all_aux,
                const_refs,
                allowed_mask,
            });
    }

    // 5. Intersect truth tables per core variable tuple and extract all entailed F_2 affine equations!
    let mut injected = 0usize;
    let _ = inc;
    for (core_vars, subs) in groups {
        let n_core = core_vars.len();
        let full_mask: u16 = ((1u32 << (1u32 << n_core)) - 1) as u16;
        let mut inter: u16 = full_mask;
        for s in &subs {
            inter &= s.allowed_mask;
        }
        if inter == full_mask {
            continue; // tautology, no constraints
        }

        // Gather merged const_refs and subclusters for proof-carrying step
        let mut merged_consts_map: HashMap<usize, (u8, usize)> = HashMap::new();
        let mut sub_proof: Vec<(Vec<usize>, Vec<usize>)> = Vec::with_capacity(subs.len());
        for s in &subs {
            sub_proof.push((s.clause_ids.clone(), s.aux_vars.clone()));
            for &(v, val, lid) in &s.const_refs {
                merged_consts_map.insert(v, (val, lid));
            }
        }
        let merged_consts: Vec<(usize, u8, usize)> = merged_consts_map
            .into_iter()
            .map(|(v, (val, lid))| (v, val, lid))
            .collect();

        if inter == 0 {
            // Local cluster contradiction -> 0 = 1!
            let step = ProofStep::LocalClusterF2Axiom {
                subclusters: sub_proof,
                core_vars: core_vars.clone(),
                const_refs: merged_consts,
                eq_vars: Vec::new(),
                rhs: 1,
            };
            let _ = alg.add_external_f2_eq(&[], 1, step, ledger);
            return (false, injected + 1);
        }

        // Test all non-empty linear masks alpha in 1..(1 << n_core)
        for alpha in 1u32..(1u32 << n_core) {
            let mut parity_seen: Option<u8> = None;
            let mut constant_parity = true;
            let mut rem = inter;
            while rem != 0 {
                let x = rem.trailing_zeros();
                rem &= rem - 1;
                let p = ((x & alpha).count_ones() & 1) as u8;
                match parity_seen {
                    None => parity_seen = Some(p),
                    Some(prev) if prev != p => {
                        constant_parity = false;
                        break;
                    }
                    _ => {}
                }
            }
            if constant_parity {
                if let Some(rhs) = parity_seen {
                    let mut eq_vars = Vec::new();
                    for ci in 0..n_core {
                        if ((alpha >> ci) & 1) == 1 {
                            eq_vars.push(core_vars[ci]);
                        }
                    }
                    let step = ProofStep::LocalClusterF2Axiom {
                        subclusters: sub_proof.clone(),
                        core_vars: core_vars.clone(),
                        const_refs: merged_consts.clone(),
                        eq_vars: eq_vars.clone(),
                        rhs,
                    };
                    injected += 1;
                    if !alg.add_external_f2_eq(&eq_vars, rhs, step, ledger) {
                        return (false, injected);
                    }
                }
            }
        }
    }

    (true, injected)
}
