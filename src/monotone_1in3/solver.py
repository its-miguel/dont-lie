"""Self-contained PD-PFGC solver for Monotone 1-in-3 SAT.

Strictly isolated from generators.py, harness.py, and any external SAT/CSP/ILP solvers.
Every candidate SAT assignment MUST pass the independent deterministic verifier.
"""

from __future__ import annotations

from dataclasses import dataclass, field
import math
import time
from typing import Any

from .bitwidth import (
    BitLedger,
    BitWidthExceededError,
    TrackedScalar,
    make_scalar,
    t_acos,
    t_cos,
    t_fmod_2pi,
    t_pi,
    t_sin,
    t_sqrt,
)
from .instance import Monotone1in3Instance, build_incidence
from .primitives import (
    CholeskyFactor,
    SparseOperators,
    build_M0,
    build_M_cert,
    cholesky_diag_margins,
    cholesky_factor,
    cholesky_solve,
    clamp_scalar,
    evaluate_dual_certificate,
    greedy_conflict_round,
    is_finite_scalar,
    threshold_round,
    walsh_fourier_clause_eval,
)
from .verifier import VerificationResult, verify_assignment


@dataclass(frozen=True)
class SolverConfig:
    """Hyperparameters, guardrails, and numerical mode for PD-PFGC."""

    max_iters: int | None = None
    max_time_sec: float | None = None
    mode: str = "float64"  # "float64" | "decimal" | "fraction"
    decimal_prec: int = 80
    max_int_bits_limit: int | None = None
    max_fraction_bits_limit: int | None = None

    # Primitive 1 (Global Unsat-Gate Collapse)
    eta_0: float = 1.0
    kappa_w: float = 2.0
    rho: float = 1.0
    alpha_k: float = 0.5

    # Primitive 2 (Fisher-Rao Torus Flow)
    mu_damp: float = 0.85
    tau_step: float = 0.12
    delta_0: float = 0.25

    # Primitive 3 (Polyrhythmic Interference & Spectral Filter)
    gamma_wf: float = 1.0
    gamma_beat: float = 0.5
    beta_min: float = 0.05
    beta_max: float = 0.80
    eta_spec: float = 0.35
    w_stall: int = 15
    eps_imp: float = 1e-4
    eps_kick: float = 0.18

    # Primitive 4 (Primal-Dual Saddle & Spectral Certificate)
    theta_pdhg: float = 1.0
    eta_d: float = 0.15
    delta_d: float = 0.02
    B_lambda: float = 20.0
    B_y: float = 50.0
    B_s: float = 256.0
    alpha_y: float = 0.15
    alpha_s: float = 0.25
    k_bt: int = 6
    eps_chol: float = 2.0**-20
    dual_update_interval: int | None = None  # None -> amortized B_cert = max(1, n_vars)
    record_iter_history: bool = True


@dataclass
class SolverResult:
    """Full result and telemetry produced by solve_pd_pfgc."""

    status: str  # "SAT" | "UNSAT_CERTIFIED" | "UNRESOLVED" | "OVERFLOW"
    assignment: tuple[int, ...] | None
    dual_certificate_value: float
    iterations: int
    runtime_sec: float
    primal_res_inf: float
    primal_res_l2: float
    integrality_gap: float
    dual_residual: float
    clause_violation_count: int
    bit_summary: dict[str, Any]
    iteration_history: list[dict[str, Any]] = field(default_factory=list)
    verification: VerificationResult | None = None
    best_candidate: tuple[int, ...] | None = None
    termination_reason: str = ""
    final_x: tuple[float, ...] = ()
    max_kappa2_cert_bound: float = 0.0


def _compute_primal_metrics(
    x_vals: list[TrackedScalar],
    r_vals: list[TrackedScalar],
    ops: SparseOperators,
    inv_sqrt_m: TrackedScalar,
) -> tuple[TrackedScalar, TrackedScalar, TrackedScalar, TrackedScalar]:
    """Return (primal_res_inf, primal_res_l2, r2_norm, integrality_gap) via BitLedger."""
    zero = ops.zero
    one = ops.one
    if not r_vals:
        res_inf = zero
        r2_norm = zero
        res_l2 = zero
    else:
        res_inf = abs(r_vals[0])
        r2_sq = zero
        for rv in r_vals:
            av = abs(rv)
            if av > res_inf:
                res_inf = av
            r2_sq = r2_sq + rv * rv
        if is_finite_scalar(r2_sq):
            r2_norm = t_sqrt(r2_sq)
            res_l2 = r2_norm * inv_sqrt_m
        else:
            r2_norm = r2_sq
            res_l2 = r2_sq

    if not x_vals:
        igap = zero
    else:
        igap = zero
        for xi in x_vals:
            d0 = abs(xi)
            d1 = abs(one - xi)
            gap_i = d0 if d0 <= d1 else d1
            if gap_i > igap:
                igap = gap_i
    return res_inf, res_l2, r2_norm, igap


def solve_pd_pfgc(
    instance: Monotone1in3Instance,
    config: SolverConfig | None = None,
) -> SolverResult:
    """Execute the PD-PFGC candidate algorithm on a Monotone 1-in-3 SAT instance."""
    t_start = time.perf_counter()
    cfg = config or SolverConfig()
    n = instance.n_vars
    m = instance.m_clauses

    ledger = BitLedger(
        max_int_bits_limit=cfg.max_int_bits_limit,
        max_fraction_bits_limit=cfg.max_fraction_bits_limit,
        raise_on_guardrail=True,
    )
    mode = cfg.mode
    dprec = cfg.decimal_prec

    # Trivial edge cases
    if m == 0:
        zero_assign = tuple([0] * n)
        ver = verify_assignment(instance, zero_assign)
        return SolverResult(
            status="SAT" if ver.is_sat else "UNRESOLVED",
            assignment=zero_assign if ver.is_sat else None,
            dual_certificate_value=0.0,
            iterations=0,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=0.0,
            primal_res_l2=0.0,
            integrality_gap=0.0,
            dual_residual=0.0,
            clause_violation_count=len(ver.violated_clauses),
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=ver,
            best_candidate=zero_assign,
            termination_reason="SAT_FOUND" if ver.is_sat else "UNRESOLVED",
            final_x=tuple(0.0 for _ in range(n)),
            max_kappa2_cert_bound=1.0,
        )

    if n == 0:
        return SolverResult(
            status="UNSAT_CERTIFIED",
            assignment=None,
            dual_certificate_value=float(m),
            iterations=0,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=1.0,
            primal_res_l2=1.0,
            integrality_gap=0.0,
            dual_residual=0.0,
            clause_violation_count=m,
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=None,
            best_candidate=None,
            termination_reason="UNSAT_CERT",
            final_x=(),
            max_kappa2_cert_bound=1.0,
        )

    max_iters = cfg.max_iters if cfg.max_iters is not None else min(1000, 15 * n + 100)
    b_cert = cfg.dual_update_interval if cfg.dual_update_interval is not None else max(1, n)
    t_anneal = max(1, int(0.75 * max_iters))
    b_s_eff_float = cfg.B_s

    try:
        inc = build_incidence(instance)
        ops = SparseOperators(inc, ledger, mode=mode, decimal_prec=dprec)

        # Scalar constants in active arithmetic mode
        one = ops.one
        zero = ops.zero
        half = ops.half
        pi_s = t_pi(ledger, mode=mode, decimal_prec=dprec)
        two_pi_s = pi_s + pi_s

        eta_0 = make_scalar(cfg.eta_0, ledger, mode=mode, decimal_prec=dprec)
        kappa_w = make_scalar(cfg.kappa_w, ledger, mode=mode, decimal_prec=dprec)
        rho = make_scalar(cfg.rho, ledger, mode=mode, decimal_prec=dprec)
        alpha_k = make_scalar(cfg.alpha_k, ledger, mode=mode, decimal_prec=dprec)
        mu_damp = make_scalar(cfg.mu_damp, ledger, mode=mode, decimal_prec=dprec)
        tau_step = make_scalar(cfg.tau_step, ledger, mode=mode, decimal_prec=dprec)
        delta_0 = make_scalar(cfg.delta_0, ledger, mode=mode, decimal_prec=dprec)
        gamma_wf = make_scalar(cfg.gamma_wf, ledger, mode=mode, decimal_prec=dprec)
        gamma_beat = make_scalar(cfg.gamma_beat, ledger, mode=mode, decimal_prec=dprec)
        beta_min_s = make_scalar(cfg.beta_min, ledger, mode=mode, decimal_prec=dprec)
        beta_span_s = make_scalar(cfg.beta_max - cfg.beta_min, ledger, mode=mode, decimal_prec=dprec)
        t_anneal_s = make_scalar(t_anneal, ledger, mode=mode, decimal_prec=dprec)
        eta_spec = make_scalar(cfg.eta_spec, ledger, mode=mode, decimal_prec=dprec)
        eps_imp_s = make_scalar(cfg.eps_imp, ledger, mode=mode, decimal_prec=dprec)
        eps_kick = make_scalar(cfg.eps_kick, ledger, mode=mode, decimal_prec=dprec)
        theta_pdhg = make_scalar(cfg.theta_pdhg, ledger, mode=mode, decimal_prec=dprec)
        eta_d = make_scalar(cfg.eta_d, ledger, mode=mode, decimal_prec=dprec)
        one_minus_damp_d = one - eta_d * make_scalar(cfg.delta_d, ledger, mode=mode, decimal_prec=dprec)
        B_lambda = make_scalar(cfg.B_lambda, ledger, mode=mode, decimal_prec=dprec)
        B_y = make_scalar(cfg.B_y, ledger, mode=mode, decimal_prec=dprec)
        B_s = make_scalar(cfg.B_s, ledger, mode=mode, decimal_prec=dprec)
        alpha_y = make_scalar(cfg.alpha_y, ledger, mode=mode, decimal_prec=dprec)
        alpha_s_s = make_scalar(cfg.alpha_s, ledger, mode=mode, decimal_prec=dprec)
        eps_chol = make_scalar(cfg.eps_chol, ledger, mode=mode, decimal_prec=dprec)
        two_eps_chol = ops.two * eps_chol
        max_deg_s = make_scalar(inc.max_degree, ledger, mode=mode, decimal_prec=dprec)
        min_s_bound = max_deg_s + two_eps_chol + one
        B_s_eff = B_s if B_s >= min_s_bound else min_s_bound
        b_s_eff_float = max(cfg.B_s, float(inc.max_degree) + 2.0 * cfg.eps_chol + 1.0)
        kappa2_bound = (18.0 * m + b_s_eff_float) / cfg.eps_chol

        m_s = make_scalar(m, ledger, mode=mode, decimal_prec=dprec)
        inv_sqrt_m_s = one / t_sqrt(m_s)
        eps_cert_floor_s = make_scalar(1e-6, ledger, mode=mode, decimal_prec=dprec)
        n_sq_s = make_scalar(n * n, ledger, mode=mode, decimal_prec=dprec)
        eps_mach_s = make_scalar(2.0**-53, ledger, mode=mode, decimal_prec=dprec)
        kappa2_bound_s = (make_scalar(18 * m, ledger, mode=mode, decimal_prec=dprec) + B_s_eff) / eps_chol
        cert_tol_coeff_s = n_sq_s * eps_mach_s * kappa2_bound_s
        budget_85 = make_scalar(0.85, ledger, mode=mode, decimal_prec=dprec)
        budget_50 = half

        omega_1 = pi_s / ops.three
        omega_2 = pi_s * half

        # Precompute M_0 = I + eta_0 A^T A = L_0 L_0^T
        M0 = build_M0(ops, eta_0)
        L0 = cholesky_factor(M0, ledger, mode=mode, decimal_prec=dprec)
        if L0 is None:
            raise RuntimeError("Unexpected non-SPD M_0")

        # Initialize torus phases phi^(0) breaking symmetry around x = 1/3
        one_third = one / ops.three
        phi_base = t_acos(one_third)
        n_plus_1 = make_scalar(n + 1, ledger, mode=mode, decimal_prec=dprec)
        phi: list[TrackedScalar] = []
        for i in range(n):
            idx_s = make_scalar(i + 1, ledger, mode=mode, decimal_prec=dprec)
            ang = (two_pi_s * idx_s) / n_plus_1
            phi.append(t_fmod_2pi(phi_base + delta_0 * t_sin(ang), mode=mode, decimal_prec=dprec))

        p = [zero] * n
        lam = [zero] * m
        x_prev: list[TrackedScalar] | None = None

        # Dual spectral certificate state: y_cert = 0, s_cert = d + 2*eps_chol*1
        y_cert = [zero] * m
        s_cert = [
            clamp_scalar(ops.degrees_s[i] + two_eps_chol, B_s_eff)
            for i in range(n)
        ]

        M_cert_init = build_M_cert(ops, s_cert)
        L_cert: CholeskyFactor | None = cholesky_factor(M_cert_init, ledger, mode=mode, decimal_prec=dprec)
        M_cert_shifted = build_M_cert(ops, s_cert, shift_diag=eps_chol)
        cert_pd_verified = cholesky_factor(M_cert_shifted, ledger, mode=mode, decimal_prec=dprec) is not None

        best_r2_norm_s: TrackedScalar | None = None
        stall_counter = 0
        best_d_spec = -math.inf
        best_candidate: tuple[int, ...] | None = None
        best_violations = m + 1
        last_res_inf = 1.0
        last_res_l2 = 1.0
        last_igap = 0.5
        last_dual_res = 0.0
        last_x: list[TrackedScalar] = [one_third] * n
        iter_history: list[dict[str, Any]] = []

        for t in range(max_iters):
            if cfg.max_time_sec is not None and (time.perf_counter() - t_start) >= cfg.max_time_sec:
                return SolverResult(
                    status="UNRESOLVED",
                    assignment=None,
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                    iterations=t,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=last_res_inf,
                    primal_res_l2=last_res_l2,
                    integrality_gap=last_igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=best_violations,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=None,
                    best_candidate=best_candidate,
                    termination_reason="TIMEOUT",
                    final_x=tuple(float(xi) for xi in last_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            ledger.begin_iteration(t)

            # 1. Manifold evaluation & residual
            sin_phi = [t_sin(ph) for ph in phi]
            sigma = [t_cos(ph) for ph in phi]
            x = [(one - sg) * half for sg in sigma]
            last_x = x

            ax = ops.apply_A(x)
            r = [ax[j] - one for j in range(m)]
            w = [one + kappa_w * (rj * rj) for rj in r]

            res_inf_s, res_l2_s, r2_norm_s, igap_s = _compute_primal_metrics(x, r, ops, inv_sqrt_m_s)
            res_inf = float(res_inf_s)
            res_l2 = float(res_l2_s)
            igap = float(igap_s)
            last_res_inf = res_inf
            last_res_l2 = res_l2
            last_igap = igap

            # Check non-finite overflow early
            if not (is_finite_scalar(res_inf_s) and is_finite_scalar(res_l2_s)):
                ledger.end_iteration()
                return SolverResult(
                    status="OVERFLOW",
                    assignment=None,
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=res_inf,
                    primal_res_l2=res_l2,
                    integrality_gap=igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=best_violations,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=None,
                    best_candidate=best_candidate,
                    termination_reason="OVERFLOW",
                    final_x=tuple(float(xi) for xi in x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            # Rounding & deterministic verifier check BEFORE updating further
            cand_thr = threshold_round(x)
            ver_thr = verify_assignment(instance, cand_thr)
            if ver_thr.is_sat:
                bit_snap = ledger.end_iteration()
                if cfg.record_iter_history:
                    iter_history.append({
                        "iteration": t,
                        "primal_res_inf": res_inf,
                        "primal_res_l2": res_l2,
                        "integrality_gap": igap,
                        "d_spec": best_d_spec,
                        **bit_snap,
                    })
                return SolverResult(
                    status="SAT",
                    assignment=tuple(cand_thr),
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else 0.0,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=res_inf,
                    primal_res_l2=res_l2,
                    integrality_gap=igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=0,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=ver_thr,
                    best_candidate=tuple(cand_thr),
                    termination_reason="SAT_FOUND",
                    final_x=tuple(float(xi) for xi in x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            cand_greedy = greedy_conflict_round(x, inc, ledger=ledger)
            ver_greedy = verify_assignment(instance, cand_greedy)
            if ver_greedy.is_sat:
                bit_snap = ledger.end_iteration()
                if cfg.record_iter_history:
                    iter_history.append({
                        "iteration": t,
                        "primal_res_inf": res_inf,
                        "primal_res_l2": res_l2,
                        "integrality_gap": igap,
                        "d_spec": best_d_spec,
                        **bit_snap,
                    })
                return SolverResult(
                    status="SAT",
                    assignment=tuple(cand_greedy),
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else 0.0,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=res_inf,
                    primal_res_l2=res_l2,
                    integrality_gap=igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=0,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=ver_greedy,
                    best_candidate=tuple(cand_greedy),
                    termination_reason="SAT_FOUND",
                    final_x=tuple(float(xi) for xi in x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            # Track best discrete candidate seen so far
            for cand, ver_c in ((cand_thr, ver_thr), (cand_greedy, ver_greedy)):
                vcount = len(ver_c.violated_clauses)
                if vcount < best_violations:
                    best_violations = vcount
                    best_candidate = tuple(cand)

            # 2. Primal-dual x-gradient
            clause_drive: list[TrackedScalar] = []
            for j in range(m):
                rj = r[j]
                beat_j = (t_sin(omega_1 * rj) / omega_1) + (t_sin(omega_2 * rj) / omega_2)
                clause_drive.append((w[j] + rho) * rj + lam[j] + gamma_beat * beat_j)

            gx_lin = ops.apply_AT(clause_drive)
            kx = ops.apply_K(x)
            g_x = [gx_lin[i] + alpha_k * kx[i] for i in range(n)]

            # 3. Fourier harmonic + Boolean pinning + Fisher-Rao pullback
            _, grad_wf = walsh_fourier_clause_eval(phi, sin_phi, sigma, w, ops)
            t_s = make_scalar(t, ledger, mode=mode, decimal_prec=dprec)
            frac_t = t_s / t_anneal_s
            if frac_t > one:
                frac_t = one
            beta_t = beta_min_s + beta_span_s * frac_t

            g_phi: list[TrackedScalar] = []
            for i in range(n):
                s_i = sin_phi[i]
                pb = half * s_i * g_x[i]
                pin = beta_t * s_i * sigma[i]
                g_phi.append(pb + gamma_wf * grad_wf[i] + pin)

            # 4. Global Gram-preconditioned & spectrally filtered descent direction
            f_g = ops.apply_F_spec(g_phi, eta_spec)
            m0_inv_fg = cholesky_solve(L0, f_g)
            g_tilde = ops.apply_F_spec(m0_inv_fg, eta_spec)

            # Stagnation check & polyrhythmic kick
            if best_r2_norm_s is None or r2_norm_s < (best_r2_norm_s - eps_imp_s):
                best_r2_norm_s = r2_norm_s
                stall_counter = 0
            else:
                stall_counter += 1

            if stall_counter >= cfg.w_stall:
                stall_counter = 0
                raw_kick: list[TrackedScalar] = []
                three_s = ops.three
                five_s = make_scalar(5, ledger, mode=mode, decimal_prec=dprec)
                for i in range(n):
                    i_s = make_scalar(i, ledger, mode=mode, decimal_prec=dprec)
                    arg1 = (two_pi_s * i_s) / three_s + t_s * omega_1
                    arg2 = (two_pi_s * i_s) / five_s + t_s * omega_2
                    raw_kick.append(t_cos(arg1) - t_cos(arg2))
                filt_kick = ops.apply_F_spec(raw_kick, eta_spec)
                xi = [eps_kick * fk for fk in filt_kick]
            else:
                xi = [zero] * n

            # 5. Geodesic torus update & over-relaxed PDHG multiplier update
            p_next: list[TrackedScalar] = []
            phi_next: list[TrackedScalar] = []
            for i in range(n):
                pi_new = mu_damp * p[i] - tau_step * g_tilde[i] + xi[i]
                p_next.append(pi_new)
                phi_next.append(t_fmod_2pi(phi[i] + pi_new, mode=mode, decimal_prec=dprec))

            if x_prev is None:
                x_bar = x
            else:
                x_bar = [x[i] + theta_pdhg * (x[i] - x_prev[i]) for i in range(n)]
            ax_bar = ops.apply_A(x_bar)
            lam_next = [
                clamp_scalar(one_minus_damp_d * lam[j] + eta_d * (ax_bar[j] - one), B_lambda)
                for j in range(m)
            ]

            dual_res_s = zero
            for i in range(n):
                dp = abs(p_next[i] - p[i])
                if dp > dual_res_s:
                    dual_res_s = dp
            for j in range(m):
                dl = abs(lam_next[j] - lam[j])
                if dl > dual_res_s:
                    dual_res_s = dl
            dual_res_val = float(dual_res_s)
            last_dual_res = dual_res_val

            p = p_next
            phi = phi_next
            x_prev = x
            lam = lam_next

            # 6. Dual spectral certificate ascent
            d_spec_float = best_d_spec
            if L_cert is not None:
                do_s_update = ((t % b_cert) == 0) and (t > 0 or b_cert == 1)
                d_spec, x_dual, b_vec, grad_y, grad_s = evaluate_dual_certificate(
                    y_cert, s_cert, L_cert, ops, compute_grad_s=do_s_update
                )
                d_spec_float = float(d_spec)
                if math.isfinite(d_spec_float) and d_spec_float > best_d_spec:
                    best_d_spec = d_spec_float

                x_dual_norm_sq_s = zero
                for xi_d in x_dual:
                    x_dual_norm_sq_s = x_dual_norm_sq_s + xi_d * xi_d
                eps_cert_s = eps_cert_floor_s + cert_tol_coeff_s * x_dual_norm_sq_s

                if cert_pd_verified and is_finite_scalar(d_spec) and d_spec > eps_cert_s:
                    bit_snap = ledger.end_iteration()
                    if cfg.record_iter_history:
                        iter_history.append({
                            "iteration": t,
                            "primal_res_inf": res_inf,
                            "primal_res_l2": res_l2,
                            "integrality_gap": igap,
                            "d_spec": d_spec_float,
                            **bit_snap,
                        })
                    return SolverResult(
                        status="UNSAT_CERTIFIED",
                        assignment=None,
                        dual_certificate_value=d_spec_float,
                        iterations=t + 1,
                        runtime_sec=time.perf_counter() - t_start,
                        primal_res_inf=res_inf,
                        primal_res_l2=res_l2,
                        integrality_gap=igap,
                        dual_residual=dual_res_val,
                        clause_violation_count=best_violations,
                        bit_summary=ledger.summary(),
                        iteration_history=iter_history,
                        verification=None,
                        best_candidate=best_candidate,
                        termination_reason="UNSAT_CERT",
                        final_x=tuple(float(xi) for xi in x),
                        max_kappa2_cert_bound=kappa2_bound,
                    )

                # Update y_cert every step
                y_cert = [
                    clamp_scalar(y_cert[j] + alpha_y * grad_y[j], B_y)
                    for j in range(m)
                ]

                # Update s_cert every b_cert steps with global backtracking + Schur-margin subset fallback
                if do_s_update:
                    step_s_scalar = alpha_s_s
                    s_accepted = False
                    for _ in range(cfg.k_bt):
                        s_cand: list[TrackedScalar] = []
                        for i in range(n):
                            sc = clamp_scalar(s_cert[i] + step_s_scalar * grad_s[i], B_s_eff)
                            if inc.degrees[i] == 0 and sc < two_eps_chol:
                                sc = two_eps_chol
                            s_cand.append(sc)
                        m_shifted = build_M_cert(ops, s_cand, shift_diag=eps_chol)
                        if cholesky_factor(m_shifted, ledger, mode=mode, decimal_prec=dprec) is not None:
                            m_full = build_M_cert(ops, s_cand)
                            new_factor = cholesky_factor(m_full, ledger, mode=mode, decimal_prec=dprec)
                            if new_factor is not None:
                                s_cert = s_cand
                                L_cert = new_factor
                                cert_pd_verified = True
                                s_accepted = True
                                break
                        step_s_scalar = step_s_scalar * half

                    if not s_accepted:
                        L_sh = cholesky_factor(
                            build_M_cert(ops, s_cert, shift_diag=eps_chol),
                            ledger,
                            mode=mode,
                            decimal_prec=dprec,
                        )
                        if L_sh is not None:
                            margins = cholesky_diag_margins(L_sh, ledger, mode=mode, decimal_prec=dprec)
                            for budget in (budget_85, budget_50):
                                s_cand = list(s_cert)
                                dec_entries: list[tuple[TrackedScalar, int, TrackedScalar]] = []
                                for i in range(n):
                                    if grad_s[i] >= zero:
                                        s_cand[i] = clamp_scalar(
                                            s_cert[i] + alpha_s_s * grad_s[i], B_s_eff
                                        )
                                    else:
                                        dec_i = -(alpha_s_s * grad_s[i])
                                        if inc.degrees[i] == 0:
                                            max_d0 = s_cert[i] - two_eps_chol
                                            if max_d0 <= zero:
                                                dec_i = zero
                                            elif dec_i > max_d0:
                                                dec_i = max_d0
                                        max_box = s_cert[i] + B_s_eff
                                        if dec_i > max_box:
                                            dec_i = max_box
                                        if dec_i > zero:
                                            dec_entries.append((dec_i / margins[i], i, dec_i))
                                dec_entries.sort(key=lambda item: item[0].value)
                                cum_ratio = zero
                                for r_i, i, dec_i in dec_entries:
                                    if cum_ratio + r_i <= budget:
                                        s_cand[i] = s_cert[i] - dec_i
                                        cum_ratio = cum_ratio + r_i
                                    else:
                                        rem = budget - cum_ratio
                                        if rem > zero:
                                            s_cand[i] = s_cert[i] - rem * margins[i]
                                        break
                                m_shifted = build_M_cert(ops, s_cand, shift_diag=eps_chol)
                                if cholesky_factor(m_shifted, ledger, mode=mode, decimal_prec=dprec) is not None:
                                    m_full = build_M_cert(ops, s_cand)
                                    new_factor = cholesky_factor(m_full, ledger, mode=mode, decimal_prec=dprec)
                                    if new_factor is not None:
                                        s_cert = s_cand
                                        L_cert = new_factor
                                        cert_pd_verified = True
                                        break

            bit_snap = ledger.end_iteration()
            if cfg.record_iter_history:
                iter_history.append({
                    "iteration": t,
                    "primal_res_inf": res_inf,
                    "primal_res_l2": res_l2,
                    "integrality_gap": igap,
                    "d_spec": d_spec_float if math.isfinite(d_spec_float) else None,
                    **bit_snap,
                })

            if ledger.nan_count > 0 or ledger.overflow_count > 0 or ledger.guardrail_tripped:
                return SolverResult(
                    status="OVERFLOW",
                    assignment=None,
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=last_res_inf,
                    primal_res_l2=last_res_l2,
                    integrality_gap=last_igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=best_violations,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=None,
                    best_candidate=best_candidate,
                    termination_reason="OVERFLOW",
                    final_x=tuple(float(xi) for xi in last_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

        return SolverResult(
            status="UNRESOLVED",
            assignment=None,
            dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
            iterations=max_iters,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=last_res_inf,
            primal_res_l2=last_res_l2,
            integrality_gap=last_igap,
            dual_residual=last_dual_res,
            clause_violation_count=best_violations,
            bit_summary=ledger.summary(),
            iteration_history=iter_history,
            verification=None,
            best_candidate=best_candidate,
            termination_reason="MAX_ITERS",
            final_x=tuple(float(xi) for xi in last_x),
            max_kappa2_cert_bound=kappa2_bound,
        )

    except BitWidthExceededError:
        return SolverResult(
            status="OVERFLOW",
            assignment=None,
            dual_certificate_value=-math.inf,
            iterations=len(ledger.iteration_bit_history),
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=math.inf,
            primal_res_l2=math.inf,
            integrality_gap=1.0,
            dual_residual=math.inf,
            clause_violation_count=m,
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=None,
            best_candidate=None,
            termination_reason="OVERFLOW",
            final_x=(),
            max_kappa2_cert_bound=(18.0 * m + b_s_eff_float) / cfg.eps_chol,
        )
