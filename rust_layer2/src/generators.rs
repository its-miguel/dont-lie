//! Deterministic High-Scale Adversarial Generators for Monotone 1-in-3 SAT (n = 150, 300, 600).
//!
//! Families:
//! - F1_random_crit: Critical-threshold random Monotone 1-in-3 SAT (alpha = 0.626).
//! - F2_planted_hard: Quiet-planted Monotone 1-in-3 SAT with balanced local degree.
//! - F3_tseitin_expander: Tseitin parity SAT/UNSAT on 3-regular expander graphs.
//! - F4_3sat_high_girth: Phase-transition 3-SAT (alpha = 4.26) & high-girth 3-SAT reduced via Schaefer 3-OR.
//! - F5_pigeonhole: Pigeonhole Principle PHP_k^{k+1} reduced to Monotone 1-in-3 SAT (UNSAT).

use std::collections::HashSet;

use crate::instance::Instance;

/// Deterministic SplitMix64 PRNG (zero external dependencies).
#[derive(Clone, Debug)]
pub struct Rng {
    state: u64,
}

impl Rng {
    pub fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    #[inline]
    pub fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.state;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }

    #[inline]
    pub fn gen_range(&mut self, upper: usize) -> usize {
        (self.next_u64() as usize) % upper
    }

    pub fn shuffle<T>(&mut self, slice: &mut [T]) {
        for i in (1..slice.len()).rev() {
            let j = self.gen_range(i + 1);
            slice.swap(i, j);
        }
    }
}

/// Clause builder with shared const_0 / const_1 gadget and exact Schaefer 3-OR encoder.
struct GadgetBuilder {
    n_vars: usize,
    clauses: Vec<[usize; 3]>,
    const_0: usize,
    const_1: usize,
    neg_cache: Vec<Option<usize>>,
}

impl GadgetBuilder {
    fn new(base_vars: usize) -> Self {
        let mut b = Self {
            n_vars: base_vars,
            clauses: Vec::new(),
            const_0: 0,
            const_1: 0,
            neg_cache: vec![None; base_vars],
        };
        // (const_0, const_0, const_1) forces const_0 = 0, const_1 = 1 uniquely!
        let c0 = b.alloc_var();
        let c1 = b.alloc_var();
        b.const_0 = c0;
        b.const_1 = c1;
        b.clauses.push([c0, c0, c1]);
        b
    }

    fn alloc_var(&mut self) -> usize {
        let id = self.n_vars;
        self.n_vars += 1;
        self.neg_cache.push(None);
        id
    }

    fn neg(&mut self, v: usize) -> usize {
        if let Some(nv) = self.neg_cache[v] {
            return nv;
        }
        let nv = self.alloc_var();
        self.neg_cache[v] = Some(nv);
        self.clauses.push([v, nv, self.const_0]);
        nv
    }

    /// Encode exact 3-OR clause (l1 | l2 | l3), where each literal is (var_idx, is_negated).
    /// Uses Schaefer's 3-clause, 4-aux gadget:
    ///   (neg(l1), a, b), (b, l2, c), (c, d, neg(l3))
    /// Exact truth table: satisfiable iff (l1 | l2 | l3) == 1.
    fn add_3or(&mut self, l1: (usize, bool), l2: (usize, bool), l3: (usize, bool)) {
        let v1 = if l1.1 { self.neg(l1.0) } else { l1.0 };
        let nv1 = if l1.1 { l1.0 } else { self.neg(l1.0) };
        let _ = v1;
        let v2 = if l2.1 { self.neg(l2.0) } else { l2.0 };
        let nv3 = if l3.1 { l3.0 } else { self.neg(l3.0) };

        let a = self.alloc_var();
        let b = self.alloc_var();
        let c = self.alloc_var();
        let d = self.alloc_var();
        self.clauses.push([nv1, a, b]);
        self.clauses.push([b, v2, c]);
        self.clauses.push([c, d, nv3]);
    }

    /// Encode exact 3-XOR constraint e1 ^ e2 ^ e3 == rhs (allowing (1,1,1) when rhs==1).
    fn add_3xor(&mut self, e1: usize, e2: usize, e3: usize, rhs: u8) {
        if rhs == 1 {
            // Forbidden: (0,0,0), (1,1,0), (1,0,1), (0,1,1)
            self.add_3or((e1, false), (e2, false), (e3, false));
            self.add_3or((e1, true), (e2, true), (e3, false));
            self.add_3or((e1, true), (e2, false), (e3, true));
            self.add_3or((e1, false), (e2, true), (e3, true));
        } else {
            // Forbidden: (1,0,0), (0,1,0), (0,0,1), (1,1,1)
            self.add_3or((e1, true), (e2, false), (e3, false));
            self.add_3or((e1, false), (e2, true), (e3, false));
            self.add_3or((e1, false), (e2, false), (e3, true));
            self.add_3or((e1, true), (e2, true), (e3, true));
        }
    }

    fn finish(mut self, id: String, family: String, ground_truth: &str, rng: &mut Rng) -> Instance {
        let n = self.n_vars;
        let mut perm: Vec<usize> = (0..n).collect();
        rng.shuffle(&mut perm);
        for cl in &mut self.clauses {
            cl[0] = perm[cl[0]];
            cl[1] = perm[cl[1]];
            cl[2] = perm[cl[2]];
            rng.shuffle(cl);
        }
        rng.shuffle(&mut self.clauses);
        Instance {
            id,
            family,
            n_vars: n,
            clauses: self.clauses,
            ground_truth: ground_truth.to_string(),
        }
    }
}

/// F1_random_crit: Critical-threshold random Monotone 1-in-3 SAT (alpha = 0.626).
pub fn gen_f1_random_crit(n: usize, seed: u64) -> Instance {
    let mut rng = Rng::new(seed);
    let m = ((n as f64) * 0.626).round() as usize;
    let mut seen: HashSet<[usize; 3]> = HashSet::with_capacity(m * 2);
    let mut clauses = Vec::with_capacity(m);
    while clauses.len() < m {
        let a = rng.gen_range(n);
        let b = rng.gen_range(n);
        let c = rng.gen_range(n);
        if a == b || a == c || b == c {
            continue;
        }
        let mut key = [a, b, c];
        key.sort_unstable();
        if seen.insert(key) {
            clauses.push([a, b, c]);
        }
    }
    Instance {
        id: format!("F1_random_crit_n{n}_s{seed}"),
        family: "F1_random_crit".to_string(),
        n_vars: n,
        clauses,
        ground_truth: "UNKNOWN".to_string(),
    }
}

/// F2_planted_hard: Quiet-planted Monotone 1-in-3 SAT with balanced local degree.
pub fn gen_f2_planted_hard(n: usize, seed: u64) -> Instance {
    let mut rng = Rng::new(seed);
    let m = ((n as f64) * 0.626).round() as usize;
    let n_ones = (n / 3).max(1);
    let mut perm: Vec<usize> = (0..n).collect();
    rng.shuffle(&mut perm);
    let ones: Vec<usize> = perm[..n_ones].to_vec();
    let zeros: Vec<usize> = perm[n_ones..].to_vec();

    let mut deg = vec![0u32; n];
    let mut seen: HashSet<[usize; 3]> = HashSet::with_capacity(m * 2);
    let mut clauses = Vec::with_capacity(m);

    // Pick lowest-degree candidates from ones and zeros (2-choice power-of-d balancing)
    let mut attempts = 0usize;
    while clauses.len() < m && attempts < m * 40 {
        attempts += 1;
        // Pick lowest-degree of 3 random ones
        let mut best_o = ones[rng.gen_range(ones.len())];
        for _ in 0..2 {
            let cand = ones[rng.gen_range(ones.len())];
            if deg[cand] < deg[best_o] {
                best_o = cand;
            }
        }
        // Pick two distinct low-degree zeros
        let mut z1 = zeros[rng.gen_range(zeros.len())];
        for _ in 0..2 {
            let cand = zeros[rng.gen_range(zeros.len())];
            if deg[cand] < deg[z1] {
                z1 = cand;
            }
        }
        let mut z2 = zeros[rng.gen_range(zeros.len())];
        for _ in 0..2 {
            let cand = zeros[rng.gen_range(zeros.len())];
            if cand != z1 && deg[cand] < deg[z2] {
                z2 = cand;
            }
        }
        if z1 == z2 {
            continue;
        }
        let mut key = [best_o, z1, z2];
        key.sort_unstable();
        if seen.insert(key) {
            let mut cl = [best_o, z1, z2];
            rng.shuffle(&mut cl);
            clauses.push(cl);
            deg[best_o] += 1;
            deg[z1] += 1;
            deg[z2] += 1;
        }
    }
    rng.shuffle(&mut clauses);
    Instance {
        id: format!("F2_planted_hard_n{n}_s{seed}"),
        family: "F2_planted_hard".to_string(),
        n_vars: n,
        clauses,
        ground_truth: "SAT".to_string(),
    }
}

/// Sample a simple connected 3-regular expander graph on `v_count` vertices (must be even >= 4).
fn sample_3regular_expander(v_count: usize, rng: &mut Rng) -> Vec<(usize, usize)> {
    loop {
        let mut stubs = Vec::with_capacity(v_count * 3);
        for v in 0..v_count {
            stubs.push(v);
            stubs.push(v);
            stubs.push(v);
        }
        rng.shuffle(&mut stubs);
        let mut edges = Vec::with_capacity(v_count * 3 / 2);
        let mut edge_set: HashSet<(usize, usize)> = HashSet::with_capacity(v_count * 3);
        let mut ok = true;
        for chunk in stubs.chunks_exact(2) {
            let (u, v) = (chunk[0], chunk[1]);
            if u == v {
                ok = false;
                break;
            }
            let e = if u < v { (u, v) } else { (v, u) };
            if !edge_set.insert(e) {
                ok = false;
                break;
            }
            edges.push(e);
        }
        if !ok {
            continue;
        }
        // Check connectivity via BFS
        let mut adj = vec![Vec::with_capacity(3); v_count];
        for &(u, v) in &edges {
            adj[u].push(v);
            adj[v].push(u);
        }
        let mut visited = vec![false; v_count];
        let mut stack = vec![0usize];
        visited[0] = true;
        let mut count = 0usize;
        while let Some(u) = stack.pop() {
            count += 1;
            for &nb in &adj[u] {
                if !visited[nb] {
                    visited[nb] = true;
                    stack.push(nb);
                }
            }
        }
        if count == v_count {
            return edges;
        }
    }
}

/// F3_tseitin_expander: Tseitin parity SAT/UNSAT on a 3-regular expander graph reduced to 1-in-3 SAT.
/// Each vertex introduces ~16 vars (4 3-OR gadgets * 4 aux) + 3 edges/2 = ~19 vars/vertex.
pub fn gen_f3_tseitin_expander(target_n: usize, expect_sat: bool, seed: u64) -> Instance {
    let mut rng = Rng::new(seed);
    // ~19 vars per vertex (1.5 edge + 1.5 neg_edge + 16 aux)
    let mut v_count = ((target_n as f64) / 19.0).round() as usize;
    if v_count < 6 {
        v_count = 6;
    }
    if v_count % 2 == 1 {
        v_count += 1;
    }
    let edges = sample_3regular_expander(v_count, &mut rng);
    let e_count = edges.len();
    let mut incident = vec![Vec::with_capacity(3); v_count];
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        incident[u].push(e_idx);
        incident[v].push(e_idx);
    }

    let mut gb = GadgetBuilder::new(e_count);
    let mut parity_sum = 0u8;
    let mut charges = vec![0u8; v_count];
    for v in 0..(v_count - 1) {
        let c = (rng.next_u64() & 1) as u8;
        charges[v] = c;
        parity_sum ^= c;
    }
    charges[v_count - 1] = if expect_sat { parity_sum } else { parity_sum ^ 1 };

    for v in 0..v_count {
        let inc_e = &incident[v];
        gb.add_3xor(inc_e[0], inc_e[1], inc_e[2], charges[v]);
    }

    let fam = if expect_sat {
        "F3_tseitin_expander_sat"
    } else {
        "F3_tseitin_expander_unsat"
    };
    gb.finish(
        format!("{fam}_t{target_n}_s{seed}"),
        fam.to_string(),
        if expect_sat { "SAT" } else { "UNSAT" },
        &mut rng,
    )
}

/// F4_3sat_high_girth: Phase-transition 3-SAT (alpha = 4.26) with high-girth pair rejection,
/// reduced via Schaefer's 3-OR gadget to Monotone 1-in-3 SAT (~target_n total vars).
pub fn gen_f4_3sat_high_girth(target_n: usize, seed: u64) -> Instance {
    let mut rng = Rng::new(seed);
    // Total vars ~ n_base * (2 + 4 * 4.26) ~ 19.04 * n_base
    let n_base = ((target_n as f64) / 19.04).round().max(6.0) as usize;
    let m_3sat = ((n_base as f64) * 4.26).round() as usize;

    let mut gb = GadgetBuilder::new(n_base);
    let mut pair_used: HashSet<(usize, usize)> = HashSet::new();
    let mut clauses_3sat: Vec<[(usize, bool); 3]> = Vec::with_capacity(m_3sat);
    let mut attempts = 0usize;

    while clauses_3sat.len() < m_3sat && attempts < m_3sat * 80 {
        attempts += 1;
        let v1 = rng.gen_range(n_base);
        let v2 = rng.gen_range(n_base);
        let v3 = rng.gen_range(n_base);
        if v1 == v2 || v1 == v3 || v2 == v3 {
            continue;
        }
        // High-girth filter during first 60% of clauses: avoid 2-cycles (shared variable pairs)
        let mut sorted = [v1, v2, v3];
        sorted.sort_unstable();
        let pairs = [(sorted[0], sorted[1]), (sorted[0], sorted[2]), (sorted[1], sorted[2])];
        if attempts < m_3sat * 25 && pairs.iter().any(|p| pair_used.contains(p)) {
            continue;
        }
        for p in pairs {
            pair_used.insert(p);
        }
        let s1 = (rng.next_u64() & 1) == 1;
        let s2 = (rng.next_u64() & 1) == 1;
        let s3 = (rng.next_u64() & 1) == 1;
        clauses_3sat.push([(v1, s1), (v2, s2), (v3, s3)]);
    }

    for [l1, l2, l3] in clauses_3sat {
        gb.add_3or(l1, l2, l3);
    }

    gb.finish(
        format!("F4_3sat_high_girth_t{target_n}_s{seed}"),
        "F4_3sat_high_girth".to_string(),
        "UNKNOWN",
        &mut rng,
    )
}

/// F5_pigeonhole: Pigeonhole Principle PHP_k^{k+1} (k+1 pigeons into k holes, strictly UNSAT).
/// Target sizes: k=5 (~143 vars ~ 150), k=7 (~334 vars ~ 300), k=9 (~637 vars ~ 600).
pub fn gen_f5_pigeonhole(target_n: usize, seed: u64) -> Instance {
    let mut rng = Rng::new(seed);
    let k = match target_n {
        0..=200 => 5usize,
        201..=450 => 7usize,
        _ => 9usize,
    };
    let pigeons = k + 1;
    let holes = k;
    let mut gb = GadgetBuilder::new(pigeons * holes);
    let p_var = |i: usize, j: usize| -> usize { i * holes + j };

    // 1. Each pigeon i occupies EXACTLY ONE hole: sum_{j=0}^{k-1} p_{i,j} == 1
    //    Encoded via linear 1-in-3 carry chain:
    //    (p_{i,0}, p_{i,1}, neg_c1) & (neg_c1, c1, const_0) => c1 = p_{i,0} + p_{i,1} <= 1
    for i in 0..pigeons {
        let mut prev = p_var(i, 0);
        for j in 1..(holes - 1) {
            let cur = p_var(i, j);
            let carry = gb.alloc_var();
            let neg_carry = gb.neg(carry);
            gb.clauses.push([prev, cur, neg_carry]);
            prev = carry;
        }
        let last = p_var(i, holes - 1);
        gb.clauses.push([prev, last, gb.const_0]);
    }

    // 2. Each hole j receives AT MOST ONE pigeon: for all i < i', p_{i,j} + p_{i',j} <= 1
    //    Encoded directly as (p_{i,j}, p_{i',j}, slack_{i,i',j})
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                let slack = gb.alloc_var();
                gb.clauses.push([p_var(i1, j), p_var(i2, j), slack]);
            }
        }
    }

    gb.finish(
        format!("F5_pigeonhole_PHP{k}_{pigeons}_s{seed}"),
        "F5_pigeonhole".to_string(),
        "UNSAT",
        &mut rng,
    )
}

/// F6_hybrid_f2_z_trap: Coupled Tseitin Expander (F_2 parity backbone) + XOR-Masked Pigeonhole (Z counting core).
///
/// - Parity backbone: satisfiable 3-regular expander Tseitin XOR system + global cut-chain forcing
///   a bridge edge `e_bridge = 0` ONLY after peeling V/2 expander gadgets and running global F_2 RREF.
/// - Counting core: PHP_k^{k+1} (UNSAT trap) or PHP_k^k (SAT decoupled control) where pigeon carry-chain
///   indicators `q_{i,j}` are XOR-masked with `e_bridge` via `q_{i,j} ^ p_{i,j} ^ e_bridge = 0`,
///   disconnecting Z hole cliques (on `p`) from Z pigeon lower bounds (on `q`) until F_2 RREF
///   derives `e_bridge = 0` and lifts `q_{i,j} = p_{i,j}` into Z cutting planes.
pub fn gen_f6_hybrid_f2_z_trap(target_n: usize, expect_sat: bool, seed: u64) -> Instance {
    let mut rng = Rng::new(seed);
    let (k, v_count, masks_per_pigeon) = match target_n {
        0..=200 => (3usize, 6usize, 1usize),
        201..=450 => (4usize, 10usize, 1usize),
        _ => (5usize, 18usize, 2usize),
    };
    let pigeons = if expect_sat { k } else { k + 1 };
    let holes = k;

    let edges = sample_3regular_expander(v_count, &mut rng);
    let e_count = edges.len();
    let mut incident = vec![Vec::with_capacity(3); v_count];
    let mut adj = vec![Vec::with_capacity(3); v_count];
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        incident[u].push(e_idx);
        incident[v].push(e_idx);
        adj[u].push(v);
        adj[v].push(u);
    }

    // Build a balanced cut S of size v_count/2 containing u0 and excluding v0 (edge 0 = (u0, v0))
    let (u0, v0) = edges[0];
    let mut in_s = vec![false; v_count];
    let mut queue = std::collections::VecDeque::new();
    in_s[u0] = true;
    queue.push_back(u0);
    let mut s_size = 1usize;
    while let Some(u) = queue.pop_front() {
        if s_size >= v_count / 2 {
            break;
        }
        for &nb in &adj[u] {
            if nb != v0 && !in_s[nb] && s_size < v_count / 2 {
                in_s[nb] = true;
                s_size += 1;
                queue.push_back(nb);
            }
        }
    }

    // Planted satisfiable edge assignment with e_bridge (edge 0) == 0
    let mut e_sol = vec![0u8; e_count];
    for e in 1..e_count {
        e_sol[e] = (rng.next_u64() & 1) as u8;
    }

    let mut charges = vec![0u8; v_count];
    for v in 0..v_count {
        let inc_e = &incident[v];
        charges[v] = e_sol[inc_e[0]] ^ e_sol[inc_e[1]] ^ e_sol[inc_e[2]];
    }

    // Base variables: [0..e_count) = Tseitin edges, [e_count .. e_count + pigeons*holes) = p_{i,j}
    let php_base = e_count;
    let mut gb = GadgetBuilder::new(e_count + pigeons * holes);
    let p_var = |i: usize, j: usize| -> usize { php_base + i * holes + j };

    // 1. Tseitin 3-XOR vertex gadgets (satisfiable!)
    for v in 0..v_count {
        let inc_e = &incident[v];
        gb.add_3xor(inc_e[0], inc_e[1], inc_e[2], charges[v]);
    }

    // 2. Global cut-chain encoding xor_{e in delta(S) \ {0}} e = xor_{v in S} charges[v]
    //    Together with the V/2 vertex equations in S, this forces e_bridge (edge 0) == 0 globally over F_2.
    let mut cut_rhs = 0u8;
    for v in 0..v_count {
        if in_s[v] {
            cut_rhs ^= charges[v];
        }
    }
    let mut other_cut_edges: Vec<usize> = Vec::new();
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        if e_idx != 0 && (in_s[u] ^ in_s[v]) {
            other_cut_edges.push(e_idx);
        }
    }
    assert!(other_cut_edges.len() >= 2, "expander cut must have >= 2 other edges");
    if other_cut_edges.len() == 2 {
        gb.add_3xor(other_cut_edges[0], other_cut_edges[1], gb.const_0, cut_rhs);
    } else if other_cut_edges.len() == 3 {
        gb.add_3xor(other_cut_edges[0], other_cut_edges[1], other_cut_edges[2], cut_rhs);
    } else {
        let mut acc = gb.alloc_var();
        gb.add_3xor(other_cut_edges[0], other_cut_edges[1], acc, 0);
        for &e_idx in &other_cut_edges[2..other_cut_edges.len() - 2] {
            let next_acc = gb.alloc_var();
            gb.add_3xor(acc, e_idx, next_acc, 0);
            acc = next_acc;
        }
        let n_ce = other_cut_edges.len();
        gb.add_3xor(acc, other_cut_edges[n_ce - 2], other_cut_edges[n_ce - 1], cut_rhs);
    }

    // 3. Pigeonhole core with XOR-masked pigeon indicators q_{i,j} = p_{i,j} ^ e_bridge
    let e_bridge = 0usize;
    for i in 0..pigeons {
        let mut slot_vars: Vec<usize> = Vec::with_capacity(holes);
        for j in 0..holes {
            let pv = p_var(i, j);
            let is_masked = (0..masks_per_pigeon).any(|m_off| j == (i + m_off) % holes);
            if is_masked {
                let qv = gb.alloc_var();
                gb.add_3xor(pv, qv, e_bridge, 0);
                slot_vars.push(qv);
            } else {
                slot_vars.push(pv);
            }
        }
        // Pigeon i carry chain: sum_j slot_vars[j] == 1
        let mut prev = slot_vars[0];
        for j in 1..(holes - 1) {
            let cur = slot_vars[j];
            let carry = gb.alloc_var();
            let neg_carry = gb.neg(carry);
            gb.clauses.push([prev, cur, neg_carry]);
            prev = carry;
        }
        let last = slot_vars[holes - 1];
        gb.clauses.push([prev, last, gb.const_0]);
    }

    // 4. Hole capacity pairwise at-most-one clauses on raw `p_{i,j}` variables
    for j in 0..holes {
        for i1 in 0..pigeons {
            for i2 in (i1 + 1)..pigeons {
                let slack = gb.alloc_var();
                gb.clauses.push([p_var(i1, j), p_var(i2, j), slack]);
            }
        }
    }

    let tag = if expect_sat { "sat_ctrl" } else { "unsat_trap" };
    gb.finish(
        format!("F6_hybrid_f2_z_{tag}_t{target_n}_s{seed}"),
        if expect_sat {
            "F6_hybrid_f2_z_sat".to_string()
        } else {
            "F6_hybrid_f2_z_unsat".to_string()
        },
        if expect_sat { "SAT" } else { "UNSAT" },
        &mut rng,
    )
}

/// Generate the 18-instance F6 hybrid F_2 + Z boundary suite (3 UNSAT traps + 3 SAT controls per scale).
pub fn generate_f6_suite(base_seed: u64) -> Vec<(usize, Instance)> {
    let mut suite = Vec::new();
    let mut s = base_seed;
    let mut next_seed = || {
        s = s.wrapping_add(1009);
        s
    };
    for &target_n in &[150usize, 300usize, 600usize] {
        for _ in 0..3 {
            suite.push((target_n, gen_f6_hybrid_f2_z_trap(target_n, false, next_seed())));
        }
        for _ in 0..3 {
            suite.push((target_n, gen_f6_hybrid_f2_z_trap(target_n, true, next_seed())));
        }
    }
    suite
}

/// Build the full high-scale adversarial Layer 2 benchmark suite across n in {150, 300, 600}.
pub fn generate_layer2_suite(base_seed: u64) -> Vec<(usize, Instance)> {
    let mut suite = Vec::new();
    let mut s = base_seed;
    let mut next_seed = || {
        s = s.wrapping_add(1009);
        s
    };

    for &target_n in &[150usize, 300usize, 600usize] {
        // 6 instances of F1_random_crit
        for _ in 0..6 {
            suite.push((target_n, gen_f1_random_crit(target_n, next_seed())));
        }
        // 5 instances of F2_planted_hard
        for _ in 0..5 {
            suite.push((target_n, gen_f2_planted_hard(target_n, next_seed())));
        }
        // 3 SAT + 3 UNSAT of F3_tseitin_expander
        for _ in 0..3 {
            suite.push((target_n, gen_f3_tseitin_expander(target_n, true, next_seed())));
        }
        for _ in 0..3 {
            suite.push((target_n, gen_f3_tseitin_expander(target_n, false, next_seed())));
        }
        // 5 instances of F4_3sat_high_girth
        for _ in 0..5 {
            suite.push((target_n, gen_f4_3sat_high_girth(target_n, next_seed())));
        }
        // 2 instances of F5_pigeonhole (permuted seeds)
        for _ in 0..2 {
            suite.push((target_n, gen_f5_pigeonhole(target_n, next_seed())));
        }
    }
    suite
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::solver::{HybridGroebnerCascade, SolveOutcome};
    use crate::verifier::verify_sat;

    #[test]
    fn test_schaefer_3or_truth_table() {
        for mask in 0u8..8 {
            let x0 = (mask >> 0) & 1;
            let x1 = (mask >> 1) & 1;
            let x2 = (mask >> 2) & 1;
            let mut gb = GadgetBuilder::new(3);
            gb.add_3or((0, false), (1, false), (2, false));
            // Force x0, x1, x2 to their truth table values
            for (v, val) in [(0, x0), (1, x1), (2, x2)] {
                if val == 1 {
                    gb.clauses.push([v, gb.const_0, gb.const_0]);
                } else {
                    gb.clauses.push([v, gb.const_1, gb.const_0]);
                }
            }
            let inst = Instance {
                id: "3or_tt".to_string(),
                family: "test".to_string(),
                n_vars: gb.n_vars,
                clauses: gb.clauses,
                ground_truth: if mask != 0 { "SAT" } else { "UNSAT" }.to_string(),
            };
            let solver = HybridGroebnerCascade::default();
            let res = solver.solve(&inst);
            if mask == 0 {
                assert_eq!(res.outcome, SolveOutcome::VerifiedUnsat);
            } else {
                assert_eq!(res.outcome, SolveOutcome::VerifiedSat);
                assert!(verify_sat(&inst, res.assignment.as_ref().unwrap()).is_sat);
            }
        }
    }

    #[test]
    fn test_tseitin_3xor_truth_table() {
        for rhs in [0u8, 1u8] {
            for mask in 0u8..8 {
                let x0 = (mask >> 0) & 1;
                let x1 = (mask >> 1) & 1;
                let x2 = (mask >> 2) & 1;
                let mut gb = GadgetBuilder::new(3);
                gb.add_3xor(0, 1, 2, rhs);
                for (v, val) in [(0, x0), (1, x1), (2, x2)] {
                    if val == 1 {
                        gb.clauses.push([v, gb.const_0, gb.const_0]);
                    } else {
                        gb.clauses.push([v, gb.const_1, gb.const_0]);
                    }
                }
                let inst = Instance {
                    id: "3xor_tt".to_string(),
                    family: "test".to_string(),
                    n_vars: gb.n_vars,
                    clauses: gb.clauses,
                    ground_truth: "UNKNOWN".to_string(),
                };
                let solver = HybridGroebnerCascade::default();
                let res = solver.solve(&inst);
                let expect_sat = (x0 ^ x1 ^ x2) == rhs;
                if expect_sat {
                    assert_eq!(res.outcome, SolveOutcome::VerifiedSat);
                } else {
                    assert_eq!(res.outcome, SolveOutcome::VerifiedUnsat);
                }
            }
        }
    }

    #[test]
    fn test_k4_3_and_small_php_unsat() {
        let k4 = Instance {
            id: "K4_3".to_string(),
            family: "test".to_string(),
            n_vars: 4,
            clauses: vec![[0, 1, 2], [0, 1, 3], [0, 2, 3], [1, 2, 3]],
            ground_truth: "UNSAT".to_string(),
        };
        let solver = HybridGroebnerCascade::default();
        let res = solver.solve(&k4);
        assert_eq!(res.outcome, SolveOutcome::VerifiedUnsat);
        assert!(res.unsat_cert_steps > 0);
    }

    #[test]
    fn test_gadget_sp_breaks_tseitin_expander_unsat() {
        let inst = gen_f3_tseitin_expander(150, false, 20261124);
        let solver = crate::solver_v25::GadgetSPCascade::default();
        let res = solver.solve(&inst);
        assert_eq!(res.outcome, SolveOutcome::VerifiedUnsat);
        assert_eq!(res.termination_reason, "GADGET_PEEL_F2_UNSAT_VERIFIED");
    }

    #[test]
    fn test_cutting_planes_refutes_pigeonhole() {
        for &target_n in &[150usize, 300usize, 600usize] {
            let inst = gen_f5_pigeonhole(target_n, 20261124);
            let solver = crate::solver_v25::GadgetSPCascade::layer275();
            let res = solver.solve(&inst);
            assert_eq!(
                res.outcome,
                SolveOutcome::VerifiedUnsat,
                "target_n={target_n}, reason={}, steps={}",
                res.termination_reason,
                res.unsat_cert_steps
            );
            assert_eq!(res.termination_reason, "CUTTING_PLANES_Z_UNSAT_VERIFIED");
            assert!(res.unsat_cert_steps > 0);
            assert!(!res.ledger.overflow);
        }
    }

    #[test]
    fn test_f6_diag() {
        for &(tn, seed) in &[(150usize, 20262134u64), (150, 20263143), (300, 20268188), (600, 20274242)] {
            let inst = gen_f6_hybrid_f2_z_trap(tn, false, seed);
            let inc = crate::instance::Incidence::build(&inst);
            let mut ledger = crate::ledger::BitLedger::new();
            let mut alg = crate::algebra::AlgebraicState::new(inst.n_vars, true, &mut ledger);
            let _ = alg.init_from_instance(&inst, &mut ledger) && alg.close(&inst, &inc, &mut ledger, 200000);
            let (_, n_inj) = crate::gadget::peel_gadgets_and_inject_f2(&inst, &inc, &mut alg, &mut ledger);
            let _ = alg.close(&inst, &inc, &mut ledger, 200000);
            let n_fixed = alg.fixed.iter().filter(|x| x.is_some()).count();
            let cp_res = crate::cutting_planes::run_cutting_planes_dual(&inst, &mut alg, &mut ledger);
            eprintln!("DIAG t{tn}_s{seed}: n={} n_inj={n_inj} n_fixed={n_fixed} cp_err={}", inst.n_vars, cp_res.is_err());
        }
    }
}
