//! Independent Deterministic Rust Verifier for SAT assignments AND UNSAT certificates.
//!
//! Strictly checks:
//! 1. SAT: x_i in {0, 1} and x_a + x_b + x_c == 1 for every raw clause.
//! 2. UNSAT: Replays an explicit proof-carrying algebraic refutation trace directly
//!    against the raw clause list over F_2[x_0..x_{n-1}] / <x_i^2 - x_i> and {0,1}
//!    1-in-3 semantics until `1 = 0` is derived.

use crate::instance::Instance;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SatVerification {
    pub is_sat: bool,
    pub violated_clauses: usize,
    pub error: Option<String>,
}

/// Independently verify a candidate {0, 1}^n assignment against raw clauses.
pub fn verify_sat(inst: &Instance, assignment: &[u8]) -> SatVerification {
    if assignment.len() != inst.n_vars {
        return SatVerification {
            is_sat: false,
            violated_clauses: inst.clauses.len(),
            error: Some(format!(
                "assignment length {} != n_vars {}",
                assignment.len(),
                inst.n_vars
            )),
        };
    }
    for (i, &v) in assignment.iter().enumerate() {
        if v > 1 {
            return SatVerification {
                is_sat: false,
                violated_clauses: inst.clauses.len(),
                error: Some(format!("non-binary entry x[{i}] = {v}")),
            };
        }
    }
    let mut violated = 0usize;
    for &[a, b, c] in &inst.clauses {
        let sum = assignment[a] + assignment[b] + assignment[c];
        if sum != 1 {
            violated += 1;
        }
    }
    SatVerification {
        is_sat: violated == 0,
        violated_clauses: violated,
        error: None,
    }
}

/// Proof-carrying algebraic refutation steps, each independently checkable in O(n) or O(1).
#[derive(Clone, Debug)]
pub enum ProofStep {
    /// From raw clause c_idx = (a, b, c): x_a ^ x_b ^ x_c = 1 (mod 2).
    /// Stored as linear lemma id.
    ClauseF2Axiom { c_idx: usize },
    /// XOR two previously derived linear equations.
    F2Xor { lhs: usize, rhs: usize },
    /// From raw clause c_idx = (a, b, c) with distinct literals u, v in clause:
    /// derive quadratic annihilator x_u * x_v = 0.
    ClauseAnnihilator { c_idx: usize, u: usize, v: usize },
    /// From raw clause c_idx = (a, a, b) with a != b: derive linear x_a = 0.
    DupLiteralZero { c_idx: usize, v: usize },
    /// From raw clause c_idx = (a, a, a): derive 1 = 0 immediately.
    TripleLiteralContradiction { c_idx: usize },
    /// Given verified linear equation `x_u ^ x_v = 0` (i.e. x_u = x_v) and
    /// verified annihilator `x_u * x_v = 0`, derive `x_u = 0` (since x_u^2 = x_u = 0).
    EquivAnnihilatorZero { eq_id: usize, u: usize, v: usize },
    /// Given verified linear equation `x_u = 1` and verified annihilator `x_u * x_v = 0`,
    /// derive linear `x_v = 0`.
    ConstOneAnnihilator { const_id: usize, u: usize, v: usize },
    /// Given verified linear `x_u = 0`, derive annihilator `x_u * x_v = 0`.
    ConstZeroAnnihilator { const_id: usize, u: usize, v: usize },
    /// Given verified linear `x_u ^ x_v = 0` and annihilator `x_u * x_w = 0`,
    /// derive annihilator `x_v * x_w = 0`.
    SubstAnnihilator { eq_id: usize, u: usize, v: usize, w: usize },
    /// Given raw clause (a, b, c) and verified annihilators `x_w * x_a = 0`, `x_w * x_b = 0`,
    /// `x_w * x_c = 0`, multiplying (x_a + x_b + x_c = 1) by x_w gives `x_w = 0`.
    ClauseMulAllZero { c_idx: usize, w: usize },
    /// Given raw clause (a, b, c) where `x_w * x_a = 0`, `x_w * x_b = 0` (so x_w <= x_c),
    /// and `x_c * x_z = 0`, derive annihilator `x_w * x_z = 0` (degree-3 S-polynomial transitivity).
    Deg3TransitivityAnnihilator { c_idx: usize, w: usize, c_lit: usize, z: usize },
    /// Given raw clause (a, b, c) and verified linear `x_a ^ x_b = 1` (so x_a + x_b = 1 in {0,1}
    /// because x_a * x_b = 0 from the clause!), derive linear `x_c = 0`.
    NegEquivClauseZero { c_idx: usize, eq_id: usize, c_lit: usize },
    /// Given verified linear `x_u = 1` and raw clause (u, b, c) with u distinct from b,c:
    /// derive `x_b = 0` (or `x_c = 0`).
    UnitOneForcesZero { c_idx: usize, const_id: usize, u: usize, target: usize },
    /// Given raw clause (a, b, c) and verified linear `x_a = 0`, `x_b = 0`:
    /// derive `x_c = 1`.
    UnitTwoZerosForceOne { c_idx: usize, z1_id: usize, z2_id: usize, target: usize },
    /// Given raw clause (a, b, c) and verified linear `x_a = 0`, `x_b = 0`, `x_c = 0`:
    /// derive `1 = 0`.
    UnitAllZeroContradiction { c_idx: usize, z1_id: usize, z2_id: usize, z3_id: usize },
    /// Given raw clause (a, b, c) and verified linear `x_a = 1`, `x_b = 1`:
    /// derive `1 = 0`.
    UnitTwoOnesContradiction { c_idx: usize, o1_id: usize, o2_id: usize },
    /// Local gadget elimination axiom: over a small subset of raw clauses `clause_ids`
    /// with core boundary variables `core_vars` (<= 4) and eliminated auxiliary variables
    /// `aux_vars` (<= 8), plus optional verified root constant lemmas `const_lemmas`,
    /// every satisfying local assignment obeys the F_2 linear equation
    /// `sum_{v in eq_vars} x_v = rhs (mod 2)`.
    /// Independently verified by exhaustive truth-table check over <= 2^(|core|+|aux|) states.
    LocalClusterF2Axiom {
        /// Each subcluster is (raw_clause_ids, local_aux_vars) with |local_aux_vars| <= 8.
        subclusters: Vec<(Vec<usize>, Vec<usize>)>,
        core_vars: Vec<usize>,
        const_refs: Vec<(usize, u8, usize)>, // (var, val, lemma_id)
        eq_vars: Vec<usize>,
        rhs: u8,
    },
    /// Lift a raw 1-in-3 clause c_idx = (a, b, c) into a Z-linear inequality:
    /// if `is_upper` is true:  x_a + x_b + x_c <= 1
    /// if `is_upper` is false: -x_a - x_b - x_c <= -1
    IntegerClauseLift {
        c_idx: usize,
        is_upper: bool,
    },
    /// Variable box bound over Z:
    /// if `is_upper` is true:  x_v <= 1
    /// if `is_upper` is false: -x_v <= 0  (i.e. x_v >= 0)
    IntegerBoxBound {
        v: usize,
        is_upper: bool,
    },
    /// Lift a verified F_2 constant lemma (x_v = val) into a Z-linear bound:
    /// if `is_upper` is true:  x_v <= val
    /// if `is_upper` is false: -x_v <= -val
    IntegerConstLift {
        const_id: usize,
        v: usize,
        val: u8,
        is_upper: bool,
    },
    /// Lift a verified F_2 binary equivalence lemma (x_u ^ x_v = 0, i.e., x_u = x_v in {0,1})
    /// into a Z-linear inequality:
    /// if `u_minus_v` is true:  x_u - x_v <= 0
    /// if `u_minus_v` is false: x_v - x_u <= 0
    IntegerEquivLift {
        eq_id: usize,
        u: usize,
        v: usize,
        u_minus_v: bool,
    },
    /// Gomory-Chvatal cutting-plane step over Z:
    /// Given non-negative integer multipliers `multipliers[k]` >= 1 on previously verified
    /// integer rows `parent_rows[k]` (a_k^T x <= b_k), verify exact divisibility of every
    /// combined coefficient A_i = sum_k multipliers[k] * a_{k,i} by `divisor >= 1`, and
    /// derive sum_i (A_i / divisor) x_i <= floor(B / divisor).
    IntegerCut {
        parent_rows: Vec<usize>,
        multipliers: Vec<i64>,
        divisor: i64,
        lhs: Vec<(usize, i64)>,
        rhs: i64,
    },
    /// Final integer contradiction: references a previously verified integer row whose
    /// LHS is identically 0 and whose RHS <= -1 (0 <= -1).
    IntegerContradiction {
        row_id: usize,
    },
    /// Root 1-step Failed-Literal elimination (strictly non-recursive, depth 1):
    /// Given that assuming `x_v = (1 - forced_val)` together with the raw clauses and
    /// already-verified root constants derives a contradiction via `sub_steps`,
    /// soundly derive the linear lemma `x_v = forced_val`.
    FailedLiteralElim {
        v: usize,
        forced_val: u8,
        /// Verified root constant lemma refs `(var, val, lemma_id)` imported into the sub-proof.
        root_const_refs: Vec<(usize, u8, usize)>,
        /// Sub-proof steps assuming `x_v = 1 - forced_val` (as lemma 0) + `root_const_refs`
        /// (as lemmas 1..k), deriving `1 = 0`.
        sub_steps: Vec<ProofStep>,
    },
}

#[derive(Clone, Debug)]
pub struct UnsatCertificate {
    pub steps: Vec<ProofStep>,
}

/// Bit-packed F_2 linear equation: words[0..n_words] hold variable coeffs, rhs in {0, 1}.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LinEq {
    words: Vec<u64>,
    rhs: u8,
}

impl LinEq {
    fn zero(n_words: usize) -> Self {
        Self {
            words: vec![0u64; n_words],
            rhs: 0,
        }
    }
    fn toggle(&mut self, v: usize) {
        self.words[v >> 6] ^= 1u64 << (v & 63);
    }
    fn is_zero_lhs(&self) -> bool {
        self.words.iter().all(|&w| w == 0)
    }
    fn is_contradiction(&self) -> bool {
        self.rhs == 1 && self.is_zero_lhs()
    }
    fn is_const(&self, v: usize, val: u8) -> bool {
        if self.rhs != val {
            return false;
        }
        let target_w = v >> 6;
        let target_mask = 1u64 << (v & 63);
        for (i, &w) in self.words.iter().enumerate() {
            if i == target_w {
                if w != target_mask {
                    return false;
                }
            } else if w != 0 {
                return false;
            }
        }
        true
    }
    fn is_pair_eq(&self, u: usize, v: usize, rhs: u8) -> bool {
        if u == v || self.rhs != rhs {
            return false;
        }
        let wu = u >> 6;
        let wv = v >> 6;
        let mu = 1u64 << (u & 63);
        let mv = 1u64 << (v & 63);
        for (i, &w) in self.words.iter().enumerate() {
            let expected = (if i == wu { mu } else { 0 }) | (if i == wv { mv } else { 0 });
            if w != expected {
                return false;
            }
        }
        true
    }
}

/// Independently verify an algebraic UNSAT refutation trace against raw clauses.
pub fn verify_unsat_certificate(inst: &Instance, cert: &UnsatCertificate) -> Result<(), String> {
    let n = inst.n_vars;
    let n_words = (n + 63) / 64;
    let mut lin_lemmas: Vec<LinEq> = Vec::with_capacity(cert.steps.len());
    // Verified Z-linear inequality rows: (sorted sparse (var, coeff), rhs) representing sum c*x_v <= rhs
    let mut int_rows: Vec<(Vec<(usize, i64)>, i64)> = Vec::new();
    // Dense symmetric bitset of verified annihilators x_u * x_v = 0
    let mut ann = vec![0u64; n * n_words];

    let has_ann = |ann: &[u64], u: usize, v: usize| -> bool {
        (ann[u * n_words + (v >> 6)] >> (v & 63)) & 1 == 1
    };
    let set_ann = |ann: &mut [u64], u: usize, v: usize| {
        ann[u * n_words + (v >> 6)] |= 1u64 << (v & 63);
        ann[v * n_words + (u >> 6)] |= 1u64 << (u & 63);
    };

    let mut derived_contradiction = false;

    for (idx, step) in cert.steps.iter().enumerate() {
        match step {
            &ProofStep::ClauseF2Axiom { c_idx } => {
                if c_idx >= inst.clauses.len() {
                    return Err(format!("step {idx}: bad clause {c_idx}"));
                }
                let [a, b, c] = inst.clauses[c_idx];
                let mut eq = LinEq::zero(n_words);
                eq.toggle(a);
                eq.toggle(b);
                eq.toggle(c);
                eq.rhs = 1;
                if eq.is_contradiction() {
                    derived_contradiction = true;
                }
                lin_lemmas.push(eq);
            }
            &ProofStep::F2Xor { lhs, rhs } => {
                if lhs >= lin_lemmas.len() || rhs >= lin_lemmas.len() {
                    return Err(format!("step {idx}: bad F2Xor refs {lhs},{rhs}"));
                }
                let mut eq = lin_lemmas[lhs].clone();
                for (w, &rw) in eq.words.iter_mut().zip(lin_lemmas[rhs].words.iter()) {
                    *w ^= rw;
                }
                eq.rhs ^= lin_lemmas[rhs].rhs;
                if eq.is_contradiction() {
                    derived_contradiction = true;
                }
                lin_lemmas.push(eq);
            }
            &ProofStep::ClauseAnnihilator { c_idx, u, v } => {
                if c_idx >= inst.clauses.len() || u == v {
                    return Err(format!("step {idx}: invalid ClauseAnnihilator"));
                }
                let cl = inst.clauses[c_idx];
                if !cl.contains(&u) || !cl.contains(&v) {
                    return Err(format!("step {idx}: literals {u},{v} not in clause {c_idx}"));
                }
                set_ann(&mut ann, u, v);
            }
            &ProofStep::DupLiteralZero { c_idx, v } => {
                if c_idx >= inst.clauses.len() {
                    return Err(format!("step {idx}: bad clause {c_idx}"));
                }
                let cl = inst.clauses[c_idx];
                let cnt = cl.iter().filter(|&&x| x == v).count();
                if cnt < 2 {
                    return Err(format!("step {idx}: {v} not duplicated in clause {c_idx}"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(v);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::TripleLiteralContradiction { c_idx } => {
                if c_idx >= inst.clauses.len() {
                    return Err(format!("step {idx}: bad clause {c_idx}"));
                }
                let [a, b, c] = inst.clauses[c_idx];
                if !(a == b && b == c) {
                    return Err(format!("step {idx}: clause {c_idx} is not triple literal"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                derived_contradiction = true;
                lin_lemmas.push(eq);
            }
            &ProofStep::EquivAnnihilatorZero { eq_id, u, v } => {
                if eq_id >= lin_lemmas.len() || !lin_lemmas[eq_id].is_pair_eq(u, v, 0) {
                    return Err(format!("step {idx}: invalid equiv ref {eq_id} for ({u},{v})"));
                }
                if !has_ann(&ann, u, v) {
                    return Err(format!("step {idx}: missing annihilator ({u},{v})"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(u);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::ConstOneAnnihilator { const_id, u, v } => {
                if const_id >= lin_lemmas.len() || !lin_lemmas[const_id].is_const(u, 1) {
                    return Err(format!("step {idx}: invalid const=1 ref {const_id} for {u}"));
                }
                if !has_ann(&ann, u, v) {
                    return Err(format!("step {idx}: missing annihilator ({u},{v})"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(v);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::ConstZeroAnnihilator { const_id, u, v } => {
                if const_id >= lin_lemmas.len() || !lin_lemmas[const_id].is_const(u, 0) {
                    return Err(format!("step {idx}: invalid const=0 ref {const_id} for {u}"));
                }
                set_ann(&mut ann, u, v);
            }
            &ProofStep::SubstAnnihilator { eq_id, u, v, w } => {
                if eq_id >= lin_lemmas.len() || !lin_lemmas[eq_id].is_pair_eq(u, v, 0) {
                    return Err(format!("step {idx}: invalid equiv ref {eq_id}"));
                }
                if !has_ann(&ann, u, w) {
                    return Err(format!("step {idx}: missing annihilator ({u},{w})"));
                }
                set_ann(&mut ann, v, w);
            }
            &ProofStep::ClauseMulAllZero { c_idx, w } => {
                if c_idx >= inst.clauses.len() {
                    return Err(format!("step {idx}: bad clause {c_idx}"));
                }
                let [a, b, c] = inst.clauses[c_idx];
                if !has_ann(&ann, w, a) || !has_ann(&ann, w, b) || !has_ann(&ann, w, c) {
                    return Err(format!(
                        "step {idx}: missing annihilators for w={w} against clause {c_idx}"
                    ));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(w);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::Deg3TransitivityAnnihilator { c_idx, w, c_lit, z } => {
                if c_idx >= inst.clauses.len() {
                    return Err(format!("step {idx}: bad clause {c_idx}"));
                }
                let cl = inst.clauses[c_idx];
                if !cl.contains(&c_lit) {
                    return Err(format!("step {idx}: c_lit {c_lit} not in clause {c_idx}"));
                }
                for &lit in &cl {
                    if lit != c_lit && !has_ann(&ann, w, lit) {
                        return Err(format!("step {idx}: missing annihilator ({w},{lit})"));
                    }
                }
                if !has_ann(&ann, c_lit, z) {
                    return Err(format!("step {idx}: missing annihilator ({c_lit},{z})"));
                }
                set_ann(&mut ann, w, z);
            }
            &ProofStep::NegEquivClauseZero { c_idx, eq_id, c_lit } => {
                if c_idx >= inst.clauses.len() || eq_id >= lin_lemmas.len() {
                    return Err(format!("step {idx}: bad refs in NegEquivClauseZero"));
                }
                let cl = inst.clauses[c_idx];
                let mut others = Vec::with_capacity(2);
                let mut found_c = false;
                for &lit in &cl {
                    if lit == c_lit && !found_c {
                        found_c = true;
                    } else {
                        others.push(lit);
                    }
                }
                if !found_c || others.len() != 2 || others[0] == others[1] {
                    return Err(format!("step {idx}: bad clause split for c_lit={c_lit}"));
                }
                if !lin_lemmas[eq_id].is_pair_eq(others[0], others[1], 1) {
                    return Err(format!("step {idx}: eq_id {eq_id} is not x_a ^ x_b = 1"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(c_lit);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitOneForcesZero { c_idx, const_id, u, target } => {
                if c_idx >= inst.clauses.len() || const_id >= lin_lemmas.len() {
                    return Err(format!("step {idx}: bad refs in UnitOneForcesZero"));
                }
                if !lin_lemmas[const_id].is_const(u, 1) {
                    return Err(format!("step {idx}: const_id not x_{u}=1"));
                }
                let cl = inst.clauses[c_idx];
                if !cl.contains(&u) || !cl.contains(&target) || u == target {
                    return Err(format!("step {idx}: invalid literals in UnitOneForcesZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(target);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitTwoZerosForceOne { c_idx, z1_id, z2_id, target } => {
                if c_idx >= inst.clauses.len() || z1_id >= lin_lemmas.len() || z2_id >= lin_lemmas.len() {
                    return Err(format!("step {idx}: bad refs in UnitTwoZerosForceOne"));
                }
                let cl = inst.clauses[c_idx];
                let mut others = Vec::with_capacity(2);
                let mut found = false;
                for &lit in &cl {
                    if lit == target && !found {
                        found = true;
                    } else {
                        others.push(lit);
                    }
                }
                if !found || others.len() != 2 || others.contains(&target) {
                    return Err(format!("step {idx}: target {target} not unique in clause {c_idx}"));
                }
                if !lin_lemmas[z1_id].is_const(others[0], 0) || !lin_lemmas[z2_id].is_const(others[1], 0) {
                    return Err(format!("step {idx}: missing x=0 lemmas for UnitTwoZerosForceOne"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(target);
                eq.rhs = 1;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitAllZeroContradiction { c_idx, z1_id, z2_id, z3_id } => {
                if c_idx >= inst.clauses.len()
                    || z1_id >= lin_lemmas.len()
                    || z2_id >= lin_lemmas.len()
                    || z3_id >= lin_lemmas.len()
                {
                    return Err(format!("step {idx}: bad refs in UnitAllZeroContradiction"));
                }
                let [a, b, c] = inst.clauses[c_idx];
                if !lin_lemmas[z1_id].is_const(a, 0)
                    || !lin_lemmas[z2_id].is_const(b, 0)
                    || !lin_lemmas[z3_id].is_const(c, 0)
                {
                    return Err(format!("step {idx}: missing x=0 lemmas for clause {c_idx}"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                derived_contradiction = true;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitTwoOnesContradiction { c_idx, o1_id, o2_id } => {
                if c_idx >= inst.clauses.len() || o1_id >= lin_lemmas.len() || o2_id >= lin_lemmas.len() {
                    return Err(format!("step {idx}: bad refs in UnitTwoOnesContradiction"));
                }
                let cl = inst.clauses[c_idx];
                let mut ones_found = 0usize;
                for &lit in &cl {
                    if lin_lemmas[o1_id].is_const(lit, 1) || lin_lemmas[o2_id].is_const(lit, 1) {
                        ones_found += 1;
                    }
                }
                if ones_found < 2 {
                    return Err(format!("step {idx}: fewer than 2 ones in clause {c_idx}"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                derived_contradiction = true;
                lin_lemmas.push(eq);
            }
            ProofStep::LocalClusterF2Axiom {
                subclusters,
                core_vars,
                const_refs,
                eq_vars,
                rhs,
            } => {
                if core_vars.len() > 4 {
                    return Err(format!("step {idx}: core_vars len > 4"));
                }
                let mut fixed_map: Vec<(usize, u8)> = Vec::with_capacity(const_refs.len());
                for &(v, val, lid) in const_refs {
                    if lid >= lin_lemmas.len() || !lin_lemmas[lid].is_const(v, val) {
                        return Err(format!("step {idx}: invalid const_ref ({v}={val}, {lid})"));
                    }
                    fixed_map.push((v, val));
                }
                for (cids, aux) in subclusters {
                    if aux.len() > 8 {
                        return Err(format!("step {idx}: subcluster aux len > 8"));
                    }
                    for &cid in cids {
                        if cid >= inst.clauses.len() {
                            return Err(format!("step {idx}: bad clause {cid}"));
                        }
                    }
                }
                // Exhaustively check all 2^|core| assignments to core_vars
                let n_core = core_vars.len();
                let mut assign = vec![2u8; n];
                for &(v, val) in &fixed_map {
                    assign[v] = val;
                }
                for mask in 0u32..(1u32 << n_core) {
                    for (ci, &cv) in core_vars.iter().enumerate() {
                        assign[cv] = ((mask >> ci) & 1) as u8;
                    }
                    // Check if EVERY subcluster has at least one local satisfying assignment
                    let mut all_sub_sat = true;
                    for (cids, aux) in subclusters {
                        let na = aux.len();
                        let mut sub_sat = false;
                        for amask in 0u32..(1u32 << na) {
                            for (ai, &av) in aux.iter().enumerate() {
                                assign[av] = ((amask >> ai) & 1) as u8;
                            }
                            let mut ok = true;
                            for &cid in cids {
                                let [a, b, c] = inst.clauses[cid];
                                let va = assign[a];
                                let vb = assign[b];
                                let vc = assign[c];
                                if va > 1 || vb > 1 || vc > 1 || (va + vb + vc) != 1 {
                                    ok = false;
                                    break;
                                }
                            }
                            if ok {
                                sub_sat = true;
                                break;
                            }
                        }
                        for &av in aux {
                            assign[av] = 2;
                        }
                        if !sub_sat {
                            all_sub_sat = false;
                            break;
                        }
                    }
                    if all_sub_sat {
                        // Every satisfying assignment MUST obey xor(eq_vars) == rhs
                        let mut parity = 0u8;
                        for &ev in eq_vars {
                            let val = assign[ev];
                            if val > 1 {
                                return Err(format!("step {idx}: eq_var {ev} unassigned"));
                            }
                            parity ^= val;
                        }
                        if parity != (*rhs & 1) {
                            return Err(format!(
                                "step {idx}: LocalClusterF2Axiom violated at mask={mask:#b}"
                            ));
                        }
                    }
                }
                let mut eq = LinEq::zero(n_words);
                for &ev in eq_vars {
                    eq.toggle(ev);
                }
                eq.rhs = *rhs & 1;
                if eq.is_contradiction() {
                    derived_contradiction = true;
                }
                lin_lemmas.push(eq);
            }
            &ProofStep::IntegerClauseLift { c_idx, is_upper } => {
                if c_idx >= inst.clauses.len() {
                    return Err(format!("step {idx}: bad clause {c_idx} in IntegerClauseLift"));
                }
                let [a, b, c] = inst.clauses[c_idx];
                let sign: i64 = if is_upper { 1 } else { -1 };
                let mut acc: std::collections::BTreeMap<usize, i64> = std::collections::BTreeMap::new();
                *acc.entry(a).or_insert(0) += sign;
                *acc.entry(b).or_insert(0) += sign;
                *acc.entry(c).or_insert(0) += sign;
                let lhs: Vec<(usize, i64)> = acc.into_iter().filter(|&(_, v)| v != 0).collect();
                int_rows.push((lhs, sign));
            }
            &ProofStep::IntegerBoxBound { v, is_upper } => {
                if v >= n {
                    return Err(format!("step {idx}: bad var {v} in IntegerBoxBound"));
                }
                if is_upper {
                    int_rows.push((vec![(v, 1)], 1));
                } else {
                    int_rows.push((vec![(v, -1)], 0));
                }
            }
            &ProofStep::IntegerConstLift { const_id, v, val, is_upper } => {
                if const_id >= lin_lemmas.len() || !lin_lemmas[const_id].is_const(v, val) {
                    return Err(format!(
                        "step {idx}: invalid const_id {const_id} for x_{v}={val} in IntegerConstLift"
                    ));
                }
                let iv = val as i64;
                if is_upper {
                    int_rows.push((vec![(v, 1)], iv));
                } else {
                    int_rows.push((vec![(v, -1)], -iv));
                }
            }
            &ProofStep::IntegerEquivLift {
                eq_id,
                u,
                v,
                u_minus_v,
            } => {
                if eq_id >= lin_lemmas.len() || u >= n || v >= n || u == v {
                    return Err(format!("step {idx}: bad IntegerEquivLift args"));
                }
                if !lin_lemmas[eq_id].is_pair_eq(u, v, 0) {
                    return Err(format!(
                        "step {idx}: lemma {eq_id} is not x_{u} ^ x_{v} = 0 in IntegerEquivLift"
                    ));
                }
                let mut terms = if u_minus_v {
                    vec![(u, 1i64), (v, -1i64)]
                } else {
                    vec![(v, 1i64), (u, -1i64)]
                };
                terms.sort_unstable_by_key(|&(var, _)| var);
                int_rows.push((terms, 0));
            }
            ProofStep::IntegerCut {
                parent_rows,
                multipliers,
                divisor,
                lhs,
                rhs,
            } => {
                let d = *divisor;
                if d < 1 {
                    return Err(format!("step {idx}: divisor {d} < 1 in IntegerCut"));
                }
                if parent_rows.is_empty() || parent_rows.len() != multipliers.len() {
                    return Err(format!("step {idx}: parent_rows/multipliers mismatch"));
                }
                let mut combined: std::collections::BTreeMap<usize, i128> =
                    std::collections::BTreeMap::new();
                let mut rhs_sum: i128 = 0;
                for (&rid, &mult) in parent_rows.iter().zip(multipliers.iter()) {
                    if rid >= int_rows.len() {
                        return Err(format!("step {idx}: bad parent row {rid} in IntegerCut"));
                    }
                    if mult < 0 {
                        return Err(format!("step {idx}: negative multiplier {mult} in IntegerCut"));
                    }
                    if mult == 0 {
                        continue;
                    }
                    let m128 = mult as i128;
                    let (ref prow_lhs, prow_rhs) = int_rows[rid];
                    for &(v, c) in prow_lhs {
                        *combined.entry(v).or_insert(0) += m128 * (c as i128);
                    }
                    rhs_sum += m128 * (prow_rhs as i128);
                }
                let d128 = d as i128;
                let mut expected_lhs: Vec<(usize, i64)> = Vec::new();
                for (v, coeff) in combined {
                    if coeff == 0 {
                        continue;
                    }
                    if coeff % d128 != 0 {
                        return Err(format!(
                            "step {idx}: coeff {coeff} on var {v} not divisible by {d}"
                        ));
                    }
                    let q = coeff / d128;
                    if q.abs() > (i64::MAX as i128) {
                        return Err(format!("step {idx}: coefficient overflow in IntegerCut"));
                    }
                    expected_lhs.push((v, q as i64));
                }
                let expected_rhs = rhs_sum.div_euclid(d128);
                if expected_rhs != (*rhs as i128) {
                    return Err(format!(
                        "step {idx}: IntegerCut rhs mismatch (expected {expected_rhs}, got {rhs})"
                    ));
                }
                let mut claimed_lhs = lhs.clone();
                claimed_lhs.sort_unstable_by_key(|&(v, _)| v);
                if expected_lhs != claimed_lhs {
                    return Err(format!("step {idx}: IntegerCut lhs mismatch"));
                }
                int_rows.push((expected_lhs, *rhs));
            }
            &ProofStep::IntegerContradiction { row_id } => {
                if row_id >= int_rows.len() {
                    return Err(format!("step {idx}: bad row_id {row_id} in IntegerContradiction"));
                }
                let (ref r_lhs, r_rhs) = int_rows[row_id];
                if !r_lhs.is_empty() || r_rhs >= 0 {
                    return Err(format!(
                        "step {idx}: row {row_id} is not 0 <= -1 (lhs len={}, rhs={r_rhs})",
                        r_lhs.len()
                    ));
                }
                derived_contradiction = true;
            }
            ProofStep::FailedLiteralElim {
                v,
                forced_val,
                root_const_refs,
                sub_steps,
            } => {
                if *v >= n || *forced_val > 1 {
                    return Err(format!("step {idx}: bad FailedLiteralElim var/val"));
                }
                let mut assumed_consts = Vec::with_capacity(1 + root_const_refs.len());
                assumed_consts.push((*v, 1 - *forced_val));
                for &(rv, rval, lid) in root_const_refs {
                    if lid >= lin_lemmas.len() || !lin_lemmas[lid].is_const(rv, rval) {
                        return Err(format!(
                            "step {idx}: bad root_const_ref ({rv}={rval}, {lid}) in FailedLiteralElim"
                        ));
                    }
                    assumed_consts.push((rv, rval));
                }
                verify_subproof_with_assumptions(inst, &assumed_consts, sub_steps)?;
                let mut eq = LinEq::zero(n_words);
                eq.toggle(*v);
                eq.rhs = *forced_val;
                lin_lemmas.push(eq);
            }
        }
    }

    if derived_contradiction {
        Ok(())
    } else {
        Err("certificate did not derive 1 = 0".to_string())
    }
}

/// Verify a depth-1 failed-literal subproof starting with `assumed_consts` as initial linear lemmas.
fn verify_subproof_with_assumptions(
    inst: &Instance,
    assumed_consts: &[(usize, u8)],
    sub_steps: &[ProofStep],
) -> Result<(), String> {
    let n = inst.n_vars;
    let n_words = (n + 63) / 64;
    let mut lin_lemmas: Vec<LinEq> = Vec::with_capacity(assumed_consts.len() + sub_steps.len());
    for &(v, val) in assumed_consts {
        let mut eq = LinEq::zero(n_words);
        eq.toggle(v);
        eq.rhs = val & 1;
        lin_lemmas.push(eq);
    }
    let mut ann = vec![0u64; n * n_words];
    let has_ann = |ann: &[u64], u: usize, v: usize| -> bool {
        (ann[u * n_words + (v >> 6)] >> (v & 63)) & 1 == 1
    };
    let set_ann = |ann: &mut [u64], u: usize, v: usize| {
        ann[u * n_words + (v >> 6)] |= 1u64 << (v & 63);
        ann[v * n_words + (u >> 6)] |= 1u64 << (u & 63);
    };
    let mut derived = false;

    for (idx, step) in sub_steps.iter().enumerate() {
        match step {
            &ProofStep::ClauseF2Axiom { c_idx } => {
                let [a, b, c] = inst.clauses[c_idx];
                let mut eq = LinEq::zero(n_words);
                eq.toggle(a);
                eq.toggle(b);
                eq.toggle(c);
                eq.rhs = 1;
                if eq.is_contradiction() {
                    derived = true;
                }
                lin_lemmas.push(eq);
            }
            &ProofStep::F2Xor { lhs, rhs } => {
                if lhs >= lin_lemmas.len() || rhs >= lin_lemmas.len() {
                    return Err(format!("substep {idx}: bad F2Xor"));
                }
                let mut eq = lin_lemmas[lhs].clone();
                for (w, &rw) in eq.words.iter_mut().zip(lin_lemmas[rhs].words.iter()) {
                    *w ^= rw;
                }
                eq.rhs ^= lin_lemmas[rhs].rhs;
                if eq.is_contradiction() {
                    derived = true;
                }
                lin_lemmas.push(eq);
            }
            &ProofStep::ClauseAnnihilator { c_idx, u, v } => {
                let cl = inst.clauses[c_idx];
                if u == v || !cl.contains(&u) || !cl.contains(&v) {
                    return Err(format!("substep {idx}: bad ClauseAnnihilator"));
                }
                set_ann(&mut ann, u, v);
            }
            &ProofStep::DupLiteralZero { c_idx, v } => {
                let cl = inst.clauses[c_idx];
                if cl.iter().filter(|&&x| x == v).count() < 2 {
                    return Err(format!("substep {idx}: bad DupLiteralZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(v);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::TripleLiteralContradiction { c_idx } => {
                let [a, b, c] = inst.clauses[c_idx];
                if !(a == b && b == c) {
                    return Err(format!("substep {idx}: bad TripleLiteral"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                derived = true;
                lin_lemmas.push(eq);
            }
            &ProofStep::EquivAnnihilatorZero { eq_id, u, v } => {
                if eq_id >= lin_lemmas.len() || !lin_lemmas[eq_id].is_pair_eq(u, v, 0) || !has_ann(&ann, u, v) {
                    return Err(format!("substep {idx}: bad EquivAnnihilatorZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(u);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::ConstOneAnnihilator { const_id, u, v } => {
                if const_id >= lin_lemmas.len() || !lin_lemmas[const_id].is_const(u, 1) || !has_ann(&ann, u, v) {
                    return Err(format!("substep {idx}: bad ConstOneAnnihilator"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(v);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::SubstAnnihilator { eq_id, u, v, w } => {
                if eq_id >= lin_lemmas.len() || !lin_lemmas[eq_id].is_pair_eq(u, v, 0) || !has_ann(&ann, u, w) {
                    return Err(format!("substep {idx}: bad SubstAnnihilator"));
                }
                set_ann(&mut ann, v, w);
            }
            &ProofStep::ClauseMulAllZero { c_idx, w } => {
                let [a, b, c] = inst.clauses[c_idx];
                if !has_ann(&ann, w, a) || !has_ann(&ann, w, b) || !has_ann(&ann, w, c) {
                    return Err(format!("substep {idx}: bad ClauseMulAllZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(w);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::Deg3TransitivityAnnihilator { c_idx, w, c_lit, z } => {
                let cl = inst.clauses[c_idx];
                if !cl.contains(&c_lit) || !has_ann(&ann, c_lit, z) {
                    return Err(format!("substep {idx}: bad Deg3Transitivity"));
                }
                for &lit in &cl {
                    if lit != c_lit && !has_ann(&ann, w, lit) {
                        return Err(format!("substep {idx}: missing ann in Deg3Transitivity"));
                    }
                }
                set_ann(&mut ann, w, z);
            }
            &ProofStep::NegEquivClauseZero { c_idx, eq_id, c_lit } => {
                let cl = inst.clauses[c_idx];
                let mut others = Vec::with_capacity(2);
                let mut found = false;
                for &lit in &cl {
                    if lit == c_lit && !found {
                        found = true;
                    } else {
                        others.push(lit);
                    }
                }
                if !found || others.len() != 2 || !lin_lemmas[eq_id].is_pair_eq(others[0], others[1], 1) {
                    return Err(format!("substep {idx}: bad NegEquivClauseZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(c_lit);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitOneForcesZero { c_idx, const_id, u, target } => {
                let cl = inst.clauses[c_idx];
                if const_id >= lin_lemmas.len() || !lin_lemmas[const_id].is_const(u, 1) || !cl.contains(&u) || !cl.contains(&target) || u == target {
                    return Err(format!("substep {idx}: bad UnitOneForcesZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(target);
                eq.rhs = 0;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitTwoZerosForceOne { c_idx, z1_id, z2_id, target } => {
                let cl = inst.clauses[c_idx];
                let mut others = Vec::with_capacity(2);
                let mut found = false;
                for &lit in &cl {
                    if lit == target && !found {
                        found = true;
                    } else {
                        others.push(lit);
                    }
                }
                if !found || others.len() != 2 || !lin_lemmas[z1_id].is_const(others[0], 0) || !lin_lemmas[z2_id].is_const(others[1], 0) {
                    return Err(format!("substep {idx}: bad UnitTwoZerosForceOne"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.toggle(target);
                eq.rhs = 1;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitAllZeroContradiction { c_idx, z1_id, z2_id, z3_id } => {
                let [a, b, c] = inst.clauses[c_idx];
                if !lin_lemmas[z1_id].is_const(a, 0) || !lin_lemmas[z2_id].is_const(b, 0) || !lin_lemmas[z3_id].is_const(c, 0) {
                    return Err(format!("substep {idx}: bad UnitAllZero"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                derived = true;
                lin_lemmas.push(eq);
            }
            &ProofStep::UnitTwoOnesContradiction { c_idx, o1_id, o2_id } => {
                let cl = inst.clauses[c_idx];
                let mut cnt = 0usize;
                for &lit in &cl {
                    if lin_lemmas[o1_id].is_const(lit, 1) || lin_lemmas[o2_id].is_const(lit, 1) {
                        cnt += 1;
                    }
                }
                if cnt < 2 {
                    return Err(format!("substep {idx}: bad UnitTwoOnes"));
                }
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                derived = true;
                lin_lemmas.push(eq);
            }
            _ => return Err(format!("substep {idx}: nested step not allowed in depth-1 subproof")),
        }
    }
    if derived {
        Ok(())
    } else {
        Err("failed-literal subproof did not derive 1 = 0".to_string())
    }
}

/// Backward-cone prune an `UnsatCertificate` to keep ONLY the exact proof steps
/// needed to derive the final `0 = 1 (mod 2)` or `0 <= -1` contradiction, remapping
/// all `lemma_id` and `row_id` references cleanly.
/// Returns `(pruned_cert, final_f2_contra_id, final_int_contra_row_id)`.
pub fn prune_certificate_for_lean(
    inst: &Instance,
    cert: &UnsatCertificate,
) -> Result<(UnsatCertificate, Option<usize>, Option<usize>), String> {
    let n = inst.n_vars;
    let n_words = (n + 63) / 64;

    // Map each lemma_id -> step index, and each int row_id -> step index
    let mut lin_step_idx: Vec<usize> = Vec::new();
    let mut int_step_idx: Vec<usize> = Vec::new();
    let mut lin_lemmas: Vec<LinEq> = Vec::new();

    let mut target_step: Option<usize> = None;
    let mut target_is_f2 = false;

    for (sidx, step) in cert.steps.iter().enumerate() {
        match step {
            &ProofStep::ClauseF2Axiom { c_idx } => {
                let [a, b, c] = inst.clauses[c_idx];
                let mut eq = LinEq::zero(n_words);
                eq.toggle(a);
                eq.toggle(b);
                eq.toggle(c);
                eq.rhs = 1;
                if eq.is_contradiction() && target_step.is_none() {
                    target_step = Some(sidx);
                    target_is_f2 = true;
                }
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::F2Xor { lhs, rhs } => {
                let mut eq = lin_lemmas[lhs].clone();
                for (w, &rw) in eq.words.iter_mut().zip(lin_lemmas[rhs].words.iter()) {
                    *w ^= rw;
                }
                eq.rhs ^= lin_lemmas[rhs].rhs;
                if eq.is_contradiction() && target_step.is_none() {
                    target_step = Some(sidx);
                    target_is_f2 = true;
                }
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::DupLiteralZero { v, .. } => {
                let mut eq = LinEq::zero(n_words);
                eq.toggle(v);
                eq.rhs = 0;
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::TripleLiteralContradiction { .. } => {
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                if target_step.is_none() {
                    target_step = Some(sidx);
                    target_is_f2 = true;
                }
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            ProofStep::LocalClusterF2Axiom { eq_vars, rhs, .. } => {
                let mut eq = LinEq::zero(n_words);
                for &ev in eq_vars {
                    eq.toggle(ev);
                }
                eq.rhs = *rhs & 1;
                if eq.is_contradiction() && target_step.is_none() {
                    target_step = Some(sidx);
                    target_is_f2 = true;
                }
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::EquivAnnihilatorZero { u, .. }
            | &ProofStep::ConstOneAnnihilator { v: u, .. }
            | &ProofStep::ClauseMulAllZero { w: u, .. }
            | &ProofStep::NegEquivClauseZero { c_lit: u, .. }
            | &ProofStep::UnitOneForcesZero { target: u, .. } => {
                let mut eq = LinEq::zero(n_words);
                eq.toggle(u);
                eq.rhs = 0;
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::UnitTwoZerosForceOne { target, .. } => {
                let mut eq = LinEq::zero(n_words);
                eq.toggle(target);
                eq.rhs = 1;
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            ProofStep::FailedLiteralElim { v, forced_val, .. } => {
                let mut eq = LinEq::zero(n_words);
                eq.toggle(*v);
                eq.rhs = *forced_val & 1;
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::UnitAllZeroContradiction { .. }
            | &ProofStep::UnitTwoOnesContradiction { .. } => {
                let mut eq = LinEq::zero(n_words);
                eq.rhs = 1;
                if target_step.is_none() {
                    target_step = Some(sidx);
                    target_is_f2 = true;
                }
                lin_lemmas.push(eq);
                lin_step_idx.push(sidx);
            }
            &ProofStep::IntegerClauseLift { .. }
            | &ProofStep::IntegerBoxBound { .. }
            | &ProofStep::IntegerConstLift { .. }
            | &ProofStep::IntegerEquivLift { .. }
            | ProofStep::IntegerCut { .. } => {
                int_step_idx.push(sidx);
            }
            &ProofStep::IntegerContradiction { .. } => {
                target_step = Some(sidx);
                target_is_f2 = false;
            }
            _ => {}
        }
    }

    let root_sidx = target_step.ok_or_else(|| "no contradiction step found".to_string())?;
    let mut needed = vec![false; cert.steps.len()];
    let mut stack = vec![root_sidx];
    needed[root_sidx] = true;

    while let Some(sidx) = stack.pop() {
        let mark_lin = |lid: usize, stack: &mut Vec<usize>, needed: &mut [bool]| {
            let dep = lin_step_idx[lid];
            if !needed[dep] {
                needed[dep] = true;
                stack.push(dep);
            }
        };
        let mark_int = |rid: usize, stack: &mut Vec<usize>, needed: &mut [bool]| {
            let dep = int_step_idx[rid];
            if !needed[dep] {
                needed[dep] = true;
                stack.push(dep);
            }
        };

        match &cert.steps[sidx] {
            ProofStep::F2Xor { lhs, rhs } => {
                mark_lin(*lhs, &mut stack, &mut needed);
                mark_lin(*rhs, &mut stack, &mut needed);
            }
            ProofStep::LocalClusterF2Axiom { const_refs, .. } => {
                for &(_, _, lid) in const_refs {
                    mark_lin(lid, &mut stack, &mut needed);
                }
            }
            ProofStep::IntegerConstLift { const_id, .. } => {
                mark_lin(*const_id, &mut stack, &mut needed);
            }
            ProofStep::IntegerEquivLift { eq_id, .. } => {
                mark_lin(*eq_id, &mut stack, &mut needed);
            }
            ProofStep::UnitOneForcesZero { const_id, .. } => {
                mark_lin(*const_id, &mut stack, &mut needed);
            }
            ProofStep::UnitTwoZerosForceOne { z1_id, z2_id, .. } => {
                mark_lin(*z1_id, &mut stack, &mut needed);
                mark_lin(*z2_id, &mut stack, &mut needed);
            }
            ProofStep::IntegerCut { parent_rows, .. } => {
                for &rid in parent_rows {
                    mark_int(rid, &mut stack, &mut needed);
                }
            }
            ProofStep::IntegerContradiction { row_id } => {
                mark_int(*row_id, &mut stack, &mut needed);
            }
            ProofStep::ClauseF2Axiom { .. }
            | ProofStep::DupLiteralZero { .. }
            | ProofStep::TripleLiteralContradiction { .. }
            | ProofStep::IntegerClauseLift { .. }
            | ProofStep::IntegerBoxBound { .. } => {}
            other => {
                return Err(format!("unsupported step in Lean cone: {other:?}"));
            }
        }
    }

    // Remap lemma_id and row_id cleanly in forward order
    let mut old_to_new_lin: Vec<Option<usize>> = vec![None; lin_step_idx.len()];
    let mut old_to_new_int: Vec<Option<usize>> = vec![None; int_step_idx.len()];
    let mut pruned_steps: Vec<ProofStep> = Vec::new();
    let mut cur_old_lin = 0usize;
    let mut cur_old_int = 0usize;
    let mut next_new_lin = 0usize;
    let mut next_new_int = 0usize;
    let mut final_f2_lid = None;
    let mut final_int_rid = None;

    for (sidx, step) in cert.steps.iter().enumerate() {
        let is_lin = matches!(
            step,
            ProofStep::ClauseF2Axiom { .. }
                | ProofStep::F2Xor { .. }
                | ProofStep::DupLiteralZero { .. }
                | ProofStep::TripleLiteralContradiction { .. }
                | ProofStep::LocalClusterF2Axiom { .. }
                | ProofStep::EquivAnnihilatorZero { .. }
                | ProofStep::ConstOneAnnihilator { .. }
                | ProofStep::ClauseMulAllZero { .. }
                | ProofStep::NegEquivClauseZero { .. }
                | ProofStep::UnitOneForcesZero { .. }
                | ProofStep::UnitTwoZerosForceOne { .. }
                | ProofStep::UnitAllZeroContradiction { .. }
                | ProofStep::UnitTwoOnesContradiction { .. }
                | ProofStep::FailedLiteralElim { .. }
        );
        let is_int = matches!(
            step,
            ProofStep::IntegerClauseLift { .. }
                | ProofStep::IntegerBoxBound { .. }
                | ProofStep::IntegerConstLift { .. }
                | ProofStep::IntegerEquivLift { .. }
                | ProofStep::IntegerCut { .. }
        );

        if needed[sidx] {
            let remapped = match step {
                &ProofStep::ClauseF2Axiom { c_idx } => ProofStep::ClauseF2Axiom { c_idx },
                &ProofStep::F2Xor { lhs, rhs } => ProofStep::F2Xor {
                    lhs: old_to_new_lin[lhs].unwrap(),
                    rhs: old_to_new_lin[rhs].unwrap(),
                },
                &ProofStep::DupLiteralZero { c_idx, v } => ProofStep::DupLiteralZero { c_idx, v },
                &ProofStep::TripleLiteralContradiction { c_idx } => {
                    ProofStep::TripleLiteralContradiction { c_idx }
                }
                ProofStep::LocalClusterF2Axiom {
                    subclusters,
                    core_vars,
                    const_refs,
                    eq_vars,
                    rhs,
                } => ProofStep::LocalClusterF2Axiom {
                    subclusters: subclusters.clone(),
                    core_vars: core_vars.clone(),
                    const_refs: const_refs
                        .iter()
                        .map(|&(v, val, lid)| (v, val, old_to_new_lin[lid].unwrap()))
                        .collect(),
                    eq_vars: eq_vars.clone(),
                    rhs: *rhs,
                },
                &ProofStep::IntegerClauseLift { c_idx, is_upper } => {
                    ProofStep::IntegerClauseLift { c_idx, is_upper }
                }
                &ProofStep::IntegerBoxBound { v, is_upper } => {
                    ProofStep::IntegerBoxBound { v, is_upper }
                }
                &ProofStep::IntegerConstLift {
                    const_id,
                    v,
                    val,
                    is_upper,
                } => ProofStep::IntegerConstLift {
                    const_id: old_to_new_lin[const_id].unwrap(),
                    v,
                    val,
                    is_upper,
                },
                &ProofStep::IntegerEquivLift {
                    eq_id,
                    u,
                    v,
                    u_minus_v,
                } => ProofStep::IntegerEquivLift {
                    eq_id: old_to_new_lin[eq_id].unwrap(),
                    u,
                    v,
                    u_minus_v,
                },
                &ProofStep::UnitOneForcesZero {
                    c_idx,
                    const_id,
                    u,
                    target,
                } => ProofStep::UnitOneForcesZero {
                    c_idx,
                    const_id: old_to_new_lin[const_id].unwrap(),
                    u,
                    target,
                },
                &ProofStep::UnitTwoZerosForceOne {
                    c_idx,
                    z1_id,
                    z2_id,
                    target,
                } => ProofStep::UnitTwoZerosForceOne {
                    c_idx,
                    z1_id: old_to_new_lin[z1_id].unwrap(),
                    z2_id: old_to_new_lin[z2_id].unwrap(),
                    target,
                },
                ProofStep::IntegerCut {
                    parent_rows,
                    multipliers,
                    divisor,
                    lhs,
                    rhs,
                } => ProofStep::IntegerCut {
                    parent_rows: parent_rows
                        .iter()
                        .map(|&rid| old_to_new_int[rid].unwrap())
                        .collect(),
                    multipliers: multipliers.clone(),
                    divisor: *divisor,
                    lhs: lhs.clone(),
                    rhs: *rhs,
                },
                &ProofStep::IntegerContradiction { row_id } => {
                    let nrid = old_to_new_int[row_id].unwrap();
                    final_int_rid = Some(nrid);
                    ProofStep::IntegerContradiction { row_id: nrid }
                }
                other => return Err(format!("unexpected step in pruned cone: {other:?}")),
            };
            pruned_steps.push(remapped);
            if is_lin {
                old_to_new_lin[cur_old_lin] = Some(next_new_lin);
                if sidx == root_sidx && target_is_f2 {
                    final_f2_lid = Some(next_new_lin);
                }
                next_new_lin += 1;
            }
            if is_int {
                old_to_new_int[cur_old_int] = Some(next_new_int);
                next_new_int += 1;
            }
        }
        if is_lin {
            cur_old_lin += 1;
        }
        if is_int {
            cur_old_int += 1;
        }
    }

    let pruned = UnsatCertificate {
        steps: pruned_steps,
    };
    verify_unsat_certificate(inst, &pruned)?;
    Ok((pruned, final_f2_lid, final_int_rid))
}

fn fmt_nat_list(xs: &[usize]) -> String {
    let inner: Vec<String> = xs.iter().map(|x| x.to_string()).collect();
    format!("[{}]", inner.join(", "))
}

/// Export a verified Rust `Instance` + `UnsatCertificate` directly to a self-contained Lean 4
/// file in `lean4_layer3/Monotone1in3Layer3/GeneratedCerts/<module_name>.lean`.
/// Returns `(raw_steps, pruned_steps)`.
pub fn export_lean_certificate(
    namespace_name: &str,
    inst: &Instance,
    cert: &UnsatCertificate,
    out_path: &std::path::Path,
) -> Result<(usize, usize), String> {
    use std::io::Write;
    let raw_steps = cert.steps.len();
    let (pruned, final_f2_lid, _final_int_rid) = prune_certificate_for_lean(inst, cert)?;
    let pruned_steps = pruned.steps.len() + usize::from(final_f2_lid.is_some());

    if let Some(parent) = out_path.parent() {
        std::fs::create_dir_all(parent).map_err(|e| e.to_string())?;
    }
    let mut f = std::fs::File::create(out_path).map_err(|e| e.to_string())?;
    writeln!(f, "import Monotone1in3Layer3.Certificate").map_err(|e| e.to_string())?;
    writeln!(f).map_err(|e| e.to_string())?;
    writeln!(
        f,
        "/-! Auto-generated by `rust_layer2 --export-cert` from `{}` (n = {}, m = {}, raw_steps = {}, pruned_steps = {}). -/",
        inst.id,
        inst.n_vars,
        inst.m_clauses(),
        raw_steps,
        pruned_steps
    )
    .map_err(|e| e.to_string())?;
    writeln!(f, "namespace Monotone1in3.{namespace_name}").map_err(|e| e.to_string())?;
    writeln!(f, "open Monotone1in3").map_err(|e| e.to_string())?;
    writeln!(f).map_err(|e| e.to_string())?;

    // Emit formula : Formula1in3 in chunks of 150 to stay well within default Lean 4 parser recursion depth
    let chunk_size = 150usize;
    let f_chunks: Vec<&[[usize; 3]]> = inst.clauses.chunks(chunk_size).collect();
    for (ci, chunk) in f_chunks.iter().enumerate() {
        writeln!(f, "private def formula_{ci} : Formula1in3 := [").map_err(|e| e.to_string())?;
        for (idx, &[a, b, c]) in chunk.iter().enumerate() {
            let sep = if idx + 1 == chunk.len() { "" } else { "," };
            writeln!(f, "  ({a}, {b}, {c}){sep}").map_err(|e| e.to_string())?;
        }
        writeln!(f, "]").map_err(|e| e.to_string())?;
    }
    let f_names: Vec<String> = (0..f_chunks.len()).map(|i| format!("formula_{i}")).collect();
    writeln!(f, "def formula : Formula1in3 := {}", f_names.join(" ++ ")).map_err(|e| e.to_string())?;
    writeln!(f).map_err(|e| e.to_string())?;

    // Emit cert : List UnifiedProofStep in chunks of 150
    let mut cert_lines: Vec<String> = Vec::with_capacity(pruned_steps);
    for step in &pruned.steps {
        let line = match step {
            ProofStep::ClauseF2Axiom { c_idx } => format!(".clauseF2Axiom {c_idx}"),
            ProofStep::F2Xor { lhs, rhs } => format!(".f2Xor {lhs} {rhs}"),
            ProofStep::DupLiteralZero { c_idx, v } => format!(".dupLiteralZero {c_idx} {v}"),
            ProofStep::TripleLiteralContradiction { c_idx } => {
                format!(".tripleLiteralContradiction {c_idx}")
            }
            ProofStep::LocalClusterF2Axiom {
                subclusters,
                core_vars,
                const_refs,
                eq_vars,
                rhs,
            } => {
                let subs: Vec<String> = subclusters
                    .iter()
                    .map(|(cids, aux)| format!("({}, {})", fmt_nat_list(cids), fmt_nat_list(aux)))
                    .collect();
                let crefs: Vec<String> = const_refs
                    .iter()
                    .map(|&(v, val, lid)| {
                        format!("({v}, {}, {lid})", if val == 1 { "true" } else { "false" })
                    })
                    .collect();
                format!(
                    ".localClusterF2 [{}] {} [{}] {} {}",
                    subs.join(", "),
                    fmt_nat_list(core_vars),
                    crefs.join(", "),
                    fmt_nat_list(eq_vars),
                    if *rhs == 1 { "true" } else { "false" }
                )
            }
            ProofStep::IntegerClauseLift { c_idx, is_upper } => {
                format!(".integerClauseLift {c_idx} {}", if *is_upper { "true" } else { "false" })
            }
            ProofStep::IntegerBoxBound { v, is_upper } => {
                format!(".integerBoxBound {v} {}", if *is_upper { "true" } else { "false" })
            }
            ProofStep::IntegerConstLift {
                const_id,
                v,
                val,
                is_upper,
            } => format!(
                ".integerConstLift {const_id} {v} {} {}",
                if *val == 1 { "true" } else { "false" },
                if *is_upper { "true" } else { "false" }
            ),
            ProofStep::IntegerEquivLift {
                eq_id,
                u,
                v,
                u_minus_v,
            } => format!(
                ".integerEquivLift {eq_id} {u} {v} {}",
                if *u_minus_v { "true" } else { "false" }
            ),
            ProofStep::UnitOneForcesZero {
                c_idx,
                const_id,
                u,
                target,
            } => format!(".unitOneForcesZero {c_idx} {const_id} {u} {target}"),
            ProofStep::UnitTwoZerosForceOne {
                c_idx,
                z1_id,
                z2_id,
                target,
            } => format!(".unitTwoZerosForceOne {c_idx} {z1_id} {z2_id} {target}"),
            ProofStep::IntegerCut {
                parent_rows,
                multipliers,
                divisor,
                ..
            } => {
                let pairs: Vec<String> = parent_rows
                    .iter()
                    .zip(multipliers.iter())
                    .map(|(&rid, &m)| format!("({rid}, {m})"))
                    .collect();
                format!(".integerCut [{}] {divisor}", pairs.join(", "))
            }
            ProofStep::IntegerContradiction { row_id } => {
                format!(".integerContradiction {row_id}")
            }
            other => return Err(format!("cannot export step {other:?}")),
        };
        cert_lines.push(line);
    }
    if let Some(lid) = final_f2_lid {
        cert_lines.push(format!(".f2Contradiction {lid}"));
    }
    let c_chunks: Vec<&[String]> = cert_lines.chunks(chunk_size).collect();
    for (ci, chunk) in c_chunks.iter().enumerate() {
        writeln!(f, "private def cert_{ci} : List UnifiedProofStep := [").map_err(|e| e.to_string())?;
        for (idx, line) in chunk.iter().enumerate() {
            let sep = if idx + 1 == chunk.len() { "" } else { "," };
            writeln!(f, "  {line}{sep}").map_err(|e| e.to_string())?;
        }
        writeln!(f, "]").map_err(|e| e.to_string())?;
    }
    let c_names: Vec<String> = (0..c_chunks.len()).map(|i| format!("cert_{i}")).collect();
    writeln!(f, "def cert : List UnifiedProofStep := {}", c_names.join(" ++ ")).map_err(|e| e.to_string())?;
    writeln!(f).map_err(|e| e.to_string())?;
    writeln!(f, "end Monotone1in3.{namespace_name}").map_err(|e| e.to_string())?;
    Ok((raw_steps, pruned_steps))
}
