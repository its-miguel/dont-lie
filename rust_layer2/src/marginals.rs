//! Phase 2 (Track D Engine): Zero-allocation LDL^T + Fisher-Rao Continuous Marginals
//! and Deterministic 1-in-3 Unit-Collapse Propagator (zero recursive backtracking).

use crate::instance::{Incidence, Instance};
use crate::ledger::BitLedger;

const TWO_PI: f64 = 2.0 * std::f64::consts::PI;

/// Reusable zero-allocation workspace for continuous marginal estimation and unit propagation.
pub struct MarginalWorkspace {
    pub n: usize,
    pub m: usize,
    pub phi: Vec<f64>,
    pub vel: Vec<f64>,
    pub x: Vec<f64>,
    pub grad: Vec<f64>,
    pub precond_grad: Vec<f64>,
    pub r: Vec<f64>,
    pub lambda: Vec<f64>,
    pub inv_diag: Vec<f64>,
    // Dense LDL^T buffers used when active_n <= 128
    pub ldlt_l: Vec<f64>,
    pub ldlt_d: Vec<f64>,
    pub ldlt_y: Vec<f64>,
    // Scratch buffers for greedy rounding
    pub order: Vec<usize>,
    pub clause_hits: Vec<u8>,
    pub cand: Vec<u8>,
}

impl MarginalWorkspace {
    pub fn new(n: usize, m: usize, inc: &Incidence, ledger: &mut BitLedger) -> Self {
        let dense_dim = n.min(128);
        let bytes = (8 * n + 2 * m + dense_dim * dense_dim + 2 * dense_dim) * 8 + n * 8 + m + n;
        ledger.record_mem_alloc(bytes);

        let mut inv_diag = vec![1.0; n];
        for i in 0..n {
            inv_diag[i] = 1.0 / (1.0 + inc.degrees[i] as f64);
        }

        Self {
            n,
            m,
            phi: vec![0.0; n],
            vel: vec![0.0; n],
            x: vec![0.0; n],
            grad: vec![0.0; n],
            precond_grad: vec![0.0; n],
            r: vec![0.0; m],
            lambda: vec![0.0; m],
            inv_diag,
            ldlt_l: vec![0.0; dense_dim * dense_dim],
            ldlt_d: vec![1.0; dense_dim],
            ldlt_y: vec![0.0; dense_dim],
            order: (0..n).collect(),
            clause_hits: vec![0u8; m],
            cand: vec![0u8; n],
        }
    }

    /// Initialize phases deterministically for restart `restart_idx`, respecting fixed variables.
    pub fn init_phases(&mut self, fixed: &[Option<u8>], restart_idx: usize) {
        let base_shift = 0.37 * (restart_idx as f64);
        for i in 0..self.n {
            match fixed[i] {
                Some(0) => {
                    self.phi[i] = 0.0;
                    self.x[i] = 0.0;
                }
                Some(_) => {
                    self.phi[i] = std::f64::consts::PI;
                    self.x[i] = 1.0;
                }
                None => {
                    // Deterministic low-discrepancy phase around x ~ 1/3 with restart perturbation
                    let frac = ((i as f64 * 0.61803398875 + base_shift) % 1.0).abs();
                    let angle = 0.95 + 0.65 * (frac - 0.5);
                    self.phi[i] = angle;
                    let s = (0.5 * angle).sin();
                    self.x[i] = s * s;
                }
            }
            self.vel[i] = 0.0;
        }
        self.lambda.fill(0.0);
    }

    /// Factorize small dense SPD normal matrix M_0 = I + A_act^T A_act via square-root-free LDL^T.
    /// Returns true iff factorization succeeded on `active_vars`.
    pub fn factor_active_ldlt(
        &mut self,
        inst: &Instance,
        active_vars: &[usize],
        var_to_act: &[Option<usize>],
        ledger: &mut BitLedger,
    ) -> bool {
        let k = active_vars.len();
        if k == 0 || k > 128 {
            return false;
        }
        for v in &mut self.ldlt_l[..k * k] {
            *v = 0.0;
        }
        for i in 0..k {
            self.ldlt_l[i * k + i] = 1.0;
        }
        // Accumulate A_act^T A_act into lower triangle of ldlt_l
        for &[a, b, c] in &inst.clauses {
            let lits = [var_to_act[a], var_to_act[b], var_to_act[c]];
            for &li in &lits {
                if let Some(i) = li {
                    for &lj in &lits {
                        if let Some(j) = lj {
                            if i >= j {
                                self.ldlt_l[i * k + j] += 1.0;
                            }
                        }
                    }
                }
            }
        }
        // In-place square-root-free L D L^T
        for i in 0..k {
            for j in 0..i {
                let mut sum = self.ldlt_l[i * k + j];
                for p in 0..j {
                    sum -= self.ldlt_l[i * k + p] * self.ldlt_d[p] * self.ldlt_l[j * k + p];
                    ledger.ldlt_ops += 2;
                }
                let val = sum / self.ldlt_d[j];
                if !val.is_finite() {
                    return false;
                }
                self.ldlt_l[i * k + j] = val;
                ledger.ldlt_ops += 1;
            }
            let mut diag = self.ldlt_l[i * k + i];
            for j in 0..i {
                let lij = self.ldlt_l[i * k + j];
                diag -= lij * lij * self.ldlt_d[j];
                ledger.ldlt_ops += 2;
            }
            if !diag.is_finite() || diag <= 1e-12 {
                return false;
            }
            self.ldlt_d[i] = diag;
            self.ldlt_l[i * k + i] = 1.0;
            ledger.record_float(diag);
        }
        true
    }

    fn solve_active_ldlt(&mut self, k: usize, active_vars: &[usize], ledger: &mut BitLedger) {
        for i in 0..k {
            let mut s = self.grad[active_vars[i]];
            for j in 0..i {
                s -= self.ldlt_l[i * k + j] * self.ldlt_y[j];
                ledger.ldlt_ops += 2;
            }
            self.ldlt_y[i] = s;
        }
        for i in (0..k).rev() {
            let mut xi = self.ldlt_y[i] / self.ldlt_d[i];
            for r in (i + 1)..k {
                xi -= self.ldlt_l[r * k + i] * self.ldlt_y[r];
                ledger.ldlt_ops += 2;
            }
            self.ldlt_y[i] = xi;
            self.precond_grad[active_vars[i]] = xi;
        }
    }

    /// Run a bounded burst of Fisher-Rao + Walsh-Hadamard primal-dual steps on active variables.
    pub fn run_marginal_burst(
        &mut self,
        inst: &Instance,
        fixed: &[Option<u8>],
        active_vars: &[usize],
        use_ldlt: bool,
        steps: usize,
        ledger: &mut BitLedger,
    ) {
        let tau = 0.14;
        let mu_damp = 0.82;
        let eta_d = 0.12;
        let b_lambda = 16.0;
        let k = active_vars.len();

        for _ in 0..steps {
            // 1. Evaluate x_i = sin^2(phi_i / 2) and clause residuals r_c = x_a + x_b + x_c - 1
            for &v in active_vars {
                let s = (0.5 * self.phi[v]).sin();
                self.x[v] = s * s;
            }
            self.grad.fill(0.0);

            for (c_idx, &[a, b, c]) in inst.clauses.iter().enumerate() {
                let xa = self.x[a];
                let xb = self.x[b];
                let xc = self.x[c];
                let rc = xa + xb + xc - 1.0;
                self.r[c_idx] = rc;

                // Dual update (clamped)
                let lam = (self.lambda[c_idx] + eta_d * rc).clamp(-b_lambda, b_lambda);
                self.lambda[c_idx] = lam;

                // Gradient of 0.5 * rc^2 + lam * rc + 0.5 * (xa*xb + xb*xc + xa*xc)
                let base_g = rc + lam;
                if fixed[a].is_none() {
                    self.grad[a] += base_g + 0.5 * (xb + xc);
                }
                if fixed[b].is_none() {
                    self.grad[b] += base_g + 0.5 * (xa + xc);
                }
                if fixed[c].is_none() {
                    self.grad[c] += base_g + 0.5 * (xa + xb);
                }
                ledger.fisher_rao_ops += 10;
            }

            // Convert dx gradient to dphi via dx/dphi = 0.5 * sin(phi)
            for &v in active_vars {
                let sin_p = self.phi[v].sin();
                let g = self.grad[v] * (0.5 * sin_p);
                self.grad[v] = g;
                ledger.record_float(g);
            }

            // Precondition gradient (LDL^T for small active sets, Jacobi diagonal for large)
            if use_ldlt && k <= 128 {
                self.solve_active_ldlt(k, active_vars, ledger);
            } else {
                for &v in active_vars {
                    self.precond_grad[v] = self.grad[v] * self.inv_diag[v];
                }
            }

            // Damped Fisher-Rao torus update
            for &v in active_vars {
                let vel = (mu_damp * self.vel[v] - tau * self.precond_grad[v]).clamp(-2.0, 2.0);
                self.vel[v] = vel;
                let mut phi = (self.phi[v] + vel) % TWO_PI;
                if phi < 0.0 {
                    phi += TWO_PI;
                }
                self.phi[v] = phi;
                ledger.fisher_rao_ops += 5;
            }
        }
        // Final x sync
        for &v in active_vars {
            let s = (0.5 * self.phi[v]).sin();
            self.x[v] = s * s;
            ledger.record_float(self.x[v]);
        }
    }

    /// Conflict-aware greedy rounding in descending order of marginal x_i, respecting fixed vars.
    pub fn greedy_round(&mut self, inc: &Incidence, fixed: &[Option<u8>]) -> &[u8] {
        self.cand.fill(0);
        self.clause_hits.fill(0);

        for i in 0..self.n {
            if let Some(1) = fixed[i] {
                self.cand[i] = 1;
                for &(c_idx, mult) in inc.clauses_of(i) {
                    self.clause_hits[c_idx] = self.clause_hits[c_idx].saturating_add(mult);
                }
            }
        }

        let x_ref = &self.x;
        self.order.sort_by(|&a, &b| {
            x_ref[b]
                .partial_cmp(&x_ref[a])
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

    /// Select the single highest-confidence unfixed variable and preferred value (0 or 1).
    pub fn pick_highest_confidence_clamp(
        &self,
        active_vars: &[usize],
        inc: &Incidence,
    ) -> Option<(usize, u8)> {
        let mut best_var = None;
        let mut best_val = 0u8;
        let mut best_score = -1.0f64;

        for &v in active_vars {
            let xv = self.x[v];
            let bias = (2.0 * xv - 1.0).abs();
            let deg_weight = 1.0 + (inc.degrees[v] as f64).ln_1p();
            let grad_conf = 1.0 / (1.0 + self.grad[v].abs());
            let score = (bias + 0.05) * deg_weight * (0.5 + 0.5 * grad_conf);
            if score > best_score {
                best_score = score;
                best_var = Some(v);
                best_val = if xv >= 0.5 { 1 } else { 0 };
            }
        }
        best_var.map(|v| (v, best_val))
    }
}
