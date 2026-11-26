//! Phase 1 (Track C Engine): Bit-packed F_2 Linear RREF + Bounded Degree-3 Boolean Groebner Closure.
//!
//! Supports optional proof-carrying trace generation at the root (before any speculative clamp)
//! so every UNSAT certificate is independently verifiable by `verifier::verify_unsat_certificate`.

use std::collections::HashMap;

use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;
use crate::verifier::{ProofStep, UnsatCertificate};

#[derive(Clone)]
pub struct F2Row {
    pub words: Vec<u64>,
    pub rhs: u8,
    pub lemma_id: usize,
}

#[derive(Clone)]
pub struct AlgebraicState {
    pub n: usize,
    pub n_words: usize,
    pub record_proof: bool,
    pub inconsistent: bool,
    pub proof_steps: Vec<ProofStep>,
    pub next_lemma_id: usize,

    // Incremental RREF pivots: pivots[col] = Some(F2Row)
    pub pivots: Vec<Option<F2Row>>,
    pub pivot_cols: Vec<usize>,

    // Known fixed constants: None = unfixed, Some(0/1) = fixed
    pub fixed: Vec<Option<u8>>,
    pub const_lemma_id: Vec<Option<usize>>,

    // Dense symmetric bit-packed quadratic annihilators: ann[u * n_words + (v >> 6)]
    pub ann: Vec<u64>,

    // Reusable scratch buffers (zero-allocation hot path)
    scratch_row: Vec<u64>,
    scratch_and: Vec<u64>,
    scratch_sig: Vec<u64>,
}

impl AlgebraicState {
    pub fn new(n: usize, record_proof: bool, ledger: &mut BitLedger) -> Self {
        let n_words = (n + 63) / 64;
        let ann_len = n * n_words;
        let est_bytes = ann_len * 8 + n * n_words * 8 + n * 32;
        ledger.record_mem_alloc(est_bytes);

        Self {
            n,
            n_words,
            record_proof,
            inconsistent: false,
            proof_steps: Vec::new(),
            next_lemma_id: 0,
            pivots: vec![None; n],
            pivot_cols: Vec::with_capacity(n),
            fixed: vec![None; n],
            const_lemma_id: vec![None; n],
            ann: vec![0u64; ann_len],
            scratch_row: vec![0u64; n_words],
            scratch_and: vec![0u64; n_words],
            scratch_sig: vec![0u64; n_words],
        }
    }

    #[inline]
    fn push_lin_step(&mut self, step: ProofStep) -> usize {
        if self.record_proof {
            self.proof_steps.push(step);
            let id = self.next_lemma_id;
            self.next_lemma_id += 1;
            id
        } else {
            0
        }
    }

    #[inline]
    fn push_ann_step(&mut self, step: ProofStep) {
        if self.record_proof {
            self.proof_steps.push(step);
        }
    }

    #[inline]
    pub fn has_ann(&self, u: usize, v: usize) -> bool {
        (self.ann[u * self.n_words + (v >> 6)] >> (v & 63)) & 1 == 1
    }

    #[inline]
    fn set_ann_raw(&mut self, u: usize, v: usize) -> bool {
        let idx1 = u * self.n_words + (v >> 6);
        let mask1 = 1u64 << (v & 63);
        if (self.ann[idx1] & mask1) != 0 {
            return false;
        }
        self.ann[idx1] |= mask1;
        let idx2 = v * self.n_words + (u >> 6);
        let mask2 = 1u64 << (u & 63);
        self.ann[idx2] |= mask2;
        true
    }

    /// Add an F_2 linear equation (given in `self.scratch_row` and `rhs`, with `lemma_id`)
    /// into incremental RREF. Returns false iff `1 = 0` is derived.
    fn add_f2_scratch(
        &mut self,
        mut rhs: u8,
        mut lemma_id: usize,
        ledger: &mut BitLedger,
    ) -> bool {
        if self.inconsistent {
            return false;
        }
        ledger.record_int(1);

        // Reduce against existing pivots
        let pcount = self.pivot_cols.len();
        for idx in 0..pcount {
            let pcol = self.pivot_cols[idx];
            if ((self.scratch_row[pcol >> 6] >> (pcol & 63)) & 1) != 0 {
                let prow = self.pivots[pcol].as_ref().unwrap();
                for w in 0..self.n_words {
                    self.scratch_row[w] ^= prow.words[w];
                }
                rhs ^= prow.rhs;
                ledger.f2_xor_ops += self.n_words as u64;
                let prow_id = prow.lemma_id;
                lemma_id = self.push_lin_step(ProofStep::F2Xor {
                    lhs: lemma_id,
                    rhs: prow_id,
                });
            }
        }

        // Find first set bit
        let mut piv: Option<usize> = None;
        for w in 0..self.n_words {
            let word = self.scratch_row[w];
            if word != 0 {
                let bit = word.trailing_zeros() as usize;
                let col = (w << 6) + bit;
                if col < self.n {
                    piv = Some(col);
                    break;
                }
            }
        }

        let Some(p) = piv else {
            if rhs == 1 {
                self.inconsistent = true;
                return false;
            }
            return true;
        };

        // Back-eliminate p from all existing pivots to maintain RREF
        let new_words = self.scratch_row.clone();
        let p_word = p >> 6;
        let p_mask = 1u64 << (p & 63);
        for idx in 0..self.pivot_cols.len() {
            let pcol = self.pivot_cols[idx];
            let has_p = {
                let prow = self.pivots[pcol].as_ref().unwrap();
                (prow.words[p_word] & p_mask) != 0
            };
            if has_p {
                let old_id = self.pivots[pcol].as_ref().unwrap().lemma_id;
                let next_id = self.push_lin_step(ProofStep::F2Xor {
                    lhs: old_id,
                    rhs: lemma_id,
                });
                let prow = self.pivots[pcol].as_mut().unwrap();
                for w in 0..self.n_words {
                    prow.words[w] ^= new_words[w];
                }
                prow.rhs ^= rhs;
                prow.lemma_id = next_id;
                ledger.f2_xor_ops += self.n_words as u64;
            }
        }

        self.pivots[p] = Some(F2Row {
            words: new_words,
            rhs,
            lemma_id,
        });
        self.pivot_cols.push(p);
        true
    }

    pub fn add_const(&mut self, v: usize, val: u8, lemma_id: usize, ledger: &mut BitLedger) -> bool {
        if let Some(cur) = self.fixed[v] {
            if cur != val {
                // Derive explicit 1 = 0 by XORing the two constant lemmas
                if self.record_proof {
                    if let Some(prev_id) = self.const_lemma_id[v] {
                        let _ = self.push_lin_step(ProofStep::F2Xor {
                            lhs: prev_id,
                            rhs: lemma_id,
                        });
                    }
                }
                self.inconsistent = true;
                return false;
            }
            return true;
        }
        self.fixed[v] = Some(val);
        self.const_lemma_id[v] = Some(lemma_id);
        self.scratch_row.fill(0);
        self.scratch_row[v >> 6] = 1u64 << (v & 63);
        self.add_f2_scratch(val & 1, lemma_id, ledger)
    }

    /// Inject an externally justified F_2 linear equation (e.g. from Local Gadget Elimination)
    /// into incremental RREF, recording its proof step when `record_proof` is active.
    pub fn add_external_f2_eq(
        &mut self,
        eq_vars: &[usize],
        rhs: u8,
        step: ProofStep,
        ledger: &mut BitLedger,
    ) -> bool {
        if self.inconsistent {
            return false;
        }
        let lid = self.push_lin_step(step);
        self.scratch_row.fill(0);
        for &v in eq_vars {
            self.scratch_row[v >> 6] ^= 1u64 << (v & 63);
        }
        self.add_f2_scratch(rhs & 1, lid, ledger)
    }

    /// Seed all raw clauses into the F_2 linear system and pairwise annihilator matrix.
    pub fn init_from_instance(&mut self, inst: &Instance, ledger: &mut BitLedger) -> bool {
        for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
            if a == b && b == c {
                let _ = self.push_lin_step(ProofStep::TripleLiteralContradiction { c_idx });
                self.inconsistent = true;
                return false;
            }
            if a == b || a == c || b == c {
                let dup = if a == b || a == c { a } else { b };
                let lid = self.push_lin_step(ProofStep::DupLiteralZero { c_idx, v: dup });
                if !self.add_const(dup, 0, lid, ledger) {
                    return false;
                }
            } else {
                // Pairwise annihilators x_a*x_b = 0, x_b*x_c = 0, x_a*x_c = 0
                if self.set_ann_raw(a, b) {
                    self.push_ann_step(ProofStep::ClauseAnnihilator { c_idx, u: a, v: b });
                }
                if self.set_ann_raw(b, c) {
                    self.push_ann_step(ProofStep::ClauseAnnihilator { c_idx, u: b, v: c });
                }
                if self.set_ann_raw(a, c) {
                    self.push_ann_step(ProofStep::ClauseAnnihilator { c_idx, u: a, v: c });
                }
            }

            // Linear F_2 axiom: x_a ^ x_b ^ x_c = 1
            self.scratch_row.fill(0);
            self.scratch_row[a >> 6] ^= 1u64 << (a & 63);
            self.scratch_row[b >> 6] ^= 1u64 << (b & 63);
            self.scratch_row[c >> 6] ^= 1u64 << (c & 63);
            let lid = self.push_lin_step(ProofStep::ClauseF2Axiom { c_idx });
            if !self.add_f2_scratch(1, lid, ledger) {
                return false;
            }
        }
        true
    }

    /// Run coupled F_2 RREF + unit propagation + quadratic annihilator + bounded degree-3
    /// S-polynomial closure to a fixed point (or until `s_poly_budget` is hit).
    pub fn close(
        &mut self,
        inst: &Instance,
        inc: &Incidence,
        ledger: &mut BitLedger,
        s_poly_budget: u64,
    ) -> bool {
        if self.inconsistent {
            return false;
        }
        let n = self.n;
        let n_words = self.n_words;
        let max_rounds = 16usize.min(n + 2);
        let mut s_used = 0u64;

        for _round in 0..max_rounds {
            let mut progress = false;

            // 1. Extract constants and binary equivalences from RREF
            let mut new_consts: Vec<(usize, u8, usize)> = Vec::new();
            let mut bin_eqs: Vec<(usize, usize, u8, usize)> = Vec::new();
            // Signature map for finding x_p1 ^ x_p2 = c across two RREF rows with identical free tail
            let mut sig_map: HashMap<Vec<u64>, (usize, u8, usize)> = HashMap::new();

            for p_idx in 0..self.pivot_cols.len() {
                let pcol = self.pivot_cols[p_idx];
                let (prow_rhs, prow_lemma_id, total_bits, other_col) = {
                    let prow = self.pivots[pcol].as_ref().unwrap();
                    let mut total_bits = 0u32;
                    let mut other_col = 0usize;
                    for w in 0..n_words {
                        let word = prow.words[w];
                        total_bits += word.count_ones();
                        if word != 0 {
                            let mut rem = word;
                            while rem != 0 {
                                let b = rem.trailing_zeros() as usize;
                                let col = (w << 6) + b;
                                if col != pcol {
                                    other_col = col;
                                }
                                rem &= rem - 1;
                            }
                        }
                    }
                    if total_bits > 2 {
                        self.scratch_sig.copy_from_slice(&prow.words);
                        self.scratch_sig[pcol >> 6] ^= 1u64 << (pcol & 63);
                    }
                    (prow.rhs, prow.lemma_id, total_bits, other_col)
                };
                if total_bits == 1 {
                    if self.fixed[pcol].is_none() {
                        new_consts.push((pcol, prow_rhs, prow_lemma_id));
                    } else if self.fixed[pcol] != Some(prow_rhs) {
                        if self.record_proof {
                            if let Some(prev_id) = self.const_lemma_id[pcol] {
                                let _ = self.push_lin_step(ProofStep::F2Xor {
                                    lhs: prev_id,
                                    rhs: prow_lemma_id,
                                });
                            }
                        }
                        self.inconsistent = true;
                        return false;
                    }
                } else if total_bits == 2 {
                    bin_eqs.push((pcol, other_col, prow_rhs, prow_lemma_id));
                } else {
                    if let Some(&(prev_pcol, prev_rhs, prev_id)) = sig_map.get(&self.scratch_sig) {
                        // XORing these two rows yields x_pcol ^ x_prev_pcol = prow.rhs ^ prev_rhs!
                        let eq_rhs = prow_rhs ^ prev_rhs;
                        let eq_id = self.push_lin_step(ProofStep::F2Xor {
                            lhs: prev_id,
                            rhs: prow_lemma_id,
                        });
                        bin_eqs.push((prev_pcol, pcol, eq_rhs, eq_id));
                    } else {
                        sig_map.insert(self.scratch_sig.clone(), (pcol, prow_rhs, prow_lemma_id));
                    }
                }
            }

            for (v, val, lid) in new_consts {
                progress = true;
                if !self.add_const(v, val, lid, ledger) {
                    return false;
                }
            }

            // 2. Deterministic 1-in-3 unit propagation from known constants
            if !self.unit_propagate(inst, ledger, &mut progress) {
                return false;
            }

            // 3. Apply constant-annihilator rules: x_u = 1 & x_u*x_v = 0 => x_v = 0
            for u in 0..n {
                if self.fixed[u] == Some(1) {
                    let u_cid = self.const_lemma_id[u].unwrap_or(0);
                    let row_base = u * n_words;
                    for w in 0..n_words {
                        let mut bits = self.ann[row_base + w];
                        while bits != 0 {
                            let b = bits.trailing_zeros() as usize;
                            let v = (w << 6) + b;
                            bits &= bits - 1;
                            if v < n && v != u && self.fixed[v] != Some(0) {
                                let lid = self.push_lin_step(ProofStep::ConstOneAnnihilator {
                                    const_id: u_cid,
                                    u,
                                    v,
                                });
                                progress = true;
                                if !self.add_const(v, 0, lid, ledger) {
                                    return false;
                                }
                            }
                        }
                    }
                }
            }

            // 4. Couple binary equivalences with quadratic annihilators & clauses
            for &(u, v, eq_rhs, eq_id) in &bin_eqs {
                if eq_rhs == 0 {
                    // x_u = x_v
                    if self.has_ann(u, v) {
                        if self.fixed[u] != Some(0) {
                            let lid = self.push_lin_step(ProofStep::EquivAnnihilatorZero {
                                eq_id,
                                u,
                                v,
                            });
                            ledger.s_poly_reductions += 1;
                            s_used += 1;
                            progress = true;
                            if !self.add_const(u, 0, lid, ledger) {
                                return false;
                            }
                        }
                    } else if s_used < s_poly_budget {
                        // SubstAnnihilator: copy annihilators between u and v
                        let u_base = u * n_words;
                        let v_base = v * n_words;
                        for w_idx in 0..n_words {
                            let diff_u_to_v = self.ann[u_base + w_idx] & !self.ann[v_base + w_idx];
                            let mut bits = diff_u_to_v;
                            while bits != 0 {
                                let b = bits.trailing_zeros() as usize;
                                let z = (w_idx << 6) + b;
                                bits &= bits - 1;
                                if z < n && z != v {
                                    if self.set_ann_raw(v, z) {
                                        self.push_ann_step(ProofStep::SubstAnnihilator {
                                            eq_id,
                                            u,
                                            v,
                                            w: z,
                                        });
                                        ledger.s_poly_reductions += 1;
                                        s_used += 1;
                                        progress = true;
                                    }
                                }
                            }
                            let diff_v_to_u = self.ann[v_base + w_idx] & !self.ann[u_base + w_idx];
                            let mut bits2 = diff_v_to_u;
                            while bits2 != 0 {
                                let b = bits2.trailing_zeros() as usize;
                                let z = (w_idx << 6) + b;
                                bits2 &= bits2 - 1;
                                if z < n && z != u {
                                    if self.set_ann_raw(u, z) {
                                        self.push_ann_step(ProofStep::SubstAnnihilator {
                                            eq_id,
                                            u: v,
                                            v: u,
                                            w: z,
                                        });
                                        ledger.s_poly_reductions += 1;
                                        s_used += 1;
                                        progress = true;
                                    }
                                }
                            }
                        }
                    }
                } else {
                    // x_u ^ x_v = 1: if u and v share a clause (u, v, c_lit), then c_lit = 0!
                    for &(c_idx, mult) in inc.clauses_of(u) {
                        if mult != 1 {
                            continue;
                        }
                        let cl = inst.clauses[c_idx];
                        if cl.contains(&v) {
                            let mut c_lit = None;
                            for &lit in &cl {
                                if lit != u && lit != v {
                                    c_lit = Some(lit);
                                    break;
                                }
                            }
                            if let Some(clit) = c_lit {
                                if self.fixed[clit] != Some(0) {
                                    let lid = self.push_lin_step(ProofStep::NegEquivClauseZero {
                                        c_idx,
                                        eq_id,
                                        c_lit: clit,
                                    });
                                    ledger.s_poly_reductions += 1;
                                    s_used += 1;
                                    progress = true;
                                    if !self.add_const(clit, 0, lid, ledger) {
                                        return false;
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // 5. Clause-literal multiplication (bit-parallel):
            // For each clause (a, b, c), any w in ann[a] & ann[b] & ann[c] forces x_w = 0!
            for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
                if s_used >= s_poly_budget {
                    break;
                }
                let ab = a * n_words;
                let bb = b * n_words;
                let cb = c * n_words;
                for w_idx in 0..n_words {
                    let mut common = self.ann[ab + w_idx] & self.ann[bb + w_idx] & self.ann[cb + w_idx];
                    ledger.s_poly_reductions += 1;
                    s_used += 1;
                    while common != 0 {
                        let bit = common.trailing_zeros() as usize;
                        let w = (w_idx << 6) + bit;
                        common &= common - 1;
                        if w < n && self.fixed[w] != Some(0) {
                            let lid = self.push_lin_step(ProofStep::ClauseMulAllZero { c_idx, w });
                            progress = true;
                            if !self.add_const(w, 0, lid, ledger) {
                                return false;
                            }
                        }
                    }
                }
            }

            // 6. Bounded Degree-3 S-polynomial Transitivity:
            // For clause (a, b, c) and each c_lit with others (o1, o2),
            // any w in ann[o1] & ann[o2] implies x_w <= x_{c_lit}, so ann[c_lit] subset ann[w]!
            if !progress && s_used < s_poly_budget {
                'deg3: for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
                    if a == b || a == c || b == c {
                        continue;
                    }
                    let triples = [(a, b, c), (a, c, b), (b, c, a)];
                    for (o1, o2, c_lit) in triples {
                        if s_used >= s_poly_budget {
                            break 'deg3;
                        }
                        let b1 = o1 * n_words;
                        let b2 = o2 * n_words;
                        let bc = c_lit * n_words;
                        for w_idx in 0..n_words {
                            self.scratch_and[w_idx] = self.ann[b1 + w_idx] & self.ann[b2 + w_idx];
                        }
                        for w_idx in 0..n_words {
                            let mut w_bits = self.scratch_and[w_idx];
                            while w_bits != 0 {
                                let b = w_bits.trailing_zeros() as usize;
                                let w = (w_idx << 6) + b;
                                w_bits &= w_bits - 1;
                                if w >= n || w == c_lit || self.fixed[w].is_some() {
                                    continue;
                                }
                                let bw = w * n_words;
                                for z_idx in 0..n_words {
                                    let mut new_z = self.ann[bc + z_idx] & !self.ann[bw + z_idx];
                                    if new_z == 0 {
                                        continue;
                                    }
                                    while new_z != 0 {
                                        let zb = new_z.trailing_zeros() as usize;
                                        let z = (z_idx << 6) + zb;
                                        new_z &= new_z - 1;
                                        if z < n && z != w {
                                            if self.set_ann_raw(w, z) {
                                                self.push_ann_step(
                                                    ProofStep::Deg3TransitivityAnnihilator {
                                                        c_idx,
                                                        w,
                                                        c_lit,
                                                        z,
                                                    },
                                                );
                                                ledger.s_poly_reductions += 1;
                                                s_used += 1;
                                                progress = true;
                                                if s_used >= s_poly_budget {
                                                    break 'deg3;
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            if !progress {
                break;
            }
        }
        !self.inconsistent
    }

    fn unit_propagate(
        &mut self,
        inst: &Instance,
        ledger: &mut BitLedger,
        progress: &mut bool,
    ) -> bool {
        let mut changed = true;
        while changed {
            changed = false;
            for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
                ledger.unit_prop_ops += 1;
                let fa = self.fixed[a];
                let fb = self.fixed[b];
                let fc = self.fixed[c];

                let mut sum_ones = 0u8;
                let mut ones_ids = [0usize; 3];
                let mut zero_cnt = 0usize;
                let mut zero_ids = [0usize; 3];
                let mut unfixed_var = None;
                let mut unfixed_cnt = 0usize;

                for &(v, fv) in &[(a, fa), (b, fb), (c, fc)] {
                    match fv {
                        Some(1) => {
                            if (sum_ones as usize) < 3 {
                                ones_ids[sum_ones as usize] = self.const_lemma_id[v].unwrap_or(0);
                            }
                            sum_ones += 1;
                        }
                        Some(0) => {
                            zero_ids[zero_cnt] = self.const_lemma_id[v].unwrap_or(0);
                            zero_cnt += 1;
                        }
                        None => {
                            unfixed_var = Some(v);
                            unfixed_cnt += 1;
                        }
                        _ => {}
                    }
                }
                ledger.record_int(sum_ones as i64);

                if sum_ones > 1 {
                    let _ = self.push_lin_step(ProofStep::UnitTwoOnesContradiction {
                        c_idx,
                        o1_id: ones_ids[0],
                        o2_id: ones_ids[1],
                    });
                    self.inconsistent = true;
                    return false;
                }
                if zero_cnt == 3 {
                    let _ = self.push_lin_step(ProofStep::UnitAllZeroContradiction {
                        c_idx,
                        z1_id: zero_ids[0],
                        z2_id: zero_ids[1],
                        z3_id: zero_ids[2],
                    });
                    self.inconsistent = true;
                    return false;
                }
                if sum_ones == 1 && unfixed_cnt > 0 {
                    let u = if fa == Some(1) {
                        a
                    } else if fb == Some(1) {
                        b
                    } else {
                        c
                    };
                    let u_id = self.const_lemma_id[u].unwrap_or(0);
                    for &v in &[a, b, c] {
                        if self.fixed[v].is_none() {
                            let lid = self.push_lin_step(ProofStep::UnitOneForcesZero {
                                c_idx,
                                const_id: u_id,
                                u,
                                target: v,
                            });
                            if !self.add_const(v, 0, lid, ledger) {
                                return false;
                            }
                            changed = true;
                            *progress = true;
                        }
                    }
                } else if sum_ones == 0 && zero_cnt == 2 && unfixed_cnt == 1 {
                    let target = unfixed_var.unwrap();
                    let lid = self.push_lin_step(ProofStep::UnitTwoZerosForceOne {
                        c_idx,
                        z1_id: zero_ids[0],
                        z2_id: zero_ids[1],
                        target,
                    });
                    if !self.add_const(target, 1, lid, ledger) {
                        return false;
                    }
                    changed = true;
                    *progress = true;
                }
            }
        }
        true
    }

    /// Extract the F_2 RREF particular solution (setting all free variables to 0).
    pub fn particular_f2_assignment(&self) -> Vec<u8> {
        let mut x = vec![0u8; self.n];
        for v in 0..self.n {
            if let Some(val) = self.fixed[v] {
                x[v] = val;
            }
        }
        for &pcol in &self.pivot_cols {
            let prow = self.pivots[pcol].as_ref().unwrap();
            x[pcol] = prow.rhs;
        }
        x
    }

    pub fn build_certificate(&self) -> UnsatCertificate {
        UnsatCertificate {
            steps: self.proof_steps.clone(),
        }
    }

    /// Bounded, strictly non-recursive (depth-1) Failed-Literal Elimination (FLP) at the root.
    ///
    /// For each unfixed variable `v` (ordered by degree descending) and test value `b in {1, 0}`,
    /// tests whether assuming `x_v = b` under Phase 1 algebraic closure derives `1 = 0`.
    /// When it does, emits an independently verifiable `ProofStep::FailedLiteralElim` forcing
    /// `x_v = 1 - b` at the root and immediately closes the root algebraic state.
    ///
    /// Returns `(still_consistent, num_eliminations)`.
    pub fn run_root_failed_literal_elim(
        &mut self,
        inst: &Instance,
        inc: &Incidence,
        ledger: &mut BitLedger,
        s_poly_budget: u64,
        max_passes: usize,
    ) -> (bool, usize) {
        if self.inconsistent {
            return (false, 0);
        }
        let n = self.n;
        let probe_budget = (s_poly_budget / (n as u64 + 1)).max(512);
        let mut total_elims = 0usize;

        let mut var_order: Vec<usize> = (0..n).collect();
        var_order.sort_by(|&a, &b| inc.degrees[b].cmp(&inc.degrees[a]).then_with(|| a.cmp(&b)));

        for _pass in 0..max_passes {
            let mut pass_progress = false;

            // Keep a lightweight non-proof clone for fast probing
            let mut base_probe = self.clone();
            base_probe.record_proof = false;
            base_probe.proof_steps.clear();

            for &v in &var_order {
                if self.fixed[v].is_some() {
                    continue;
                }
                for test_val in [1u8, 0u8] {
                    if self.fixed[v].is_some() {
                        break;
                    }
                    let mut probe = base_probe.clone();
                    let ok = probe.add_const(v, test_val, 0, ledger)
                        && probe.close(inst, inc, ledger, probe_budget);
                    if ok {
                        continue;
                    }

                    // Candidate failed literal found: `x_v = test_val` => contradiction!
                    // Reconstruct clean depth-1 subproof from raw clauses + verified root constants.
                    let forced_val = test_val ^ 1;
                    let mut root_const_refs: Vec<(usize, u8, usize)> = Vec::new();
                    let mut sub_steps: Vec<ProofStep> = Vec::new();

                    if self.record_proof {
                        let mut sub_alg = AlgebraicState::new(n, true, ledger);
                        let mut assumed_id = 0usize;
                        let _ = sub_alg.add_const(v, test_val, assumed_id, ledger);
                        assumed_id += 1;
                        for rv in 0..n {
                            if rv != v {
                                if let (Some(rval), Some(rlid)) =
                                    (self.fixed[rv], self.const_lemma_id[rv])
                                {
                                    root_const_refs.push((rv, rval, rlid));
                                    let _ = sub_alg.add_const(rv, rval, assumed_id, ledger);
                                    assumed_id += 1;
                                }
                            }
                        }
                        sub_alg.next_lemma_id = assumed_id;
                        let sub_ok = sub_alg.init_from_instance(inst, ledger)
                            && sub_alg.close(inst, inc, ledger, probe_budget * 2);
                        if sub_ok || !sub_alg.inconsistent {
                            // Subproof relied on non-constant root facts (e.g. gadget eqs); skip safely
                            continue;
                        }
                        sub_steps = sub_alg.proof_steps;
                    }

                    let lid = self.push_lin_step(ProofStep::FailedLiteralElim {
                        v,
                        forced_val,
                        root_const_refs,
                        sub_steps,
                    });
                    total_elims += 1;
                    pass_progress = true;

                    let root_ok = self.add_const(v, forced_val, lid, ledger)
                        && self.close(inst, inc, ledger, s_poly_budget);
                    if !root_ok {
                        return (false, total_elims);
                    }

                    // Refresh base_probe with newly forced constants/equations
                    base_probe = self.clone();
                    base_probe.record_proof = false;
                    base_probe.proof_steps.clear();
                    break;
                }
            }

            if !pass_progress {
                break;
            }
        }

        (!self.inconsistent, total_elims)
    }
}
