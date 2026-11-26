"""Track D: Single-Pass Primal-Dual Marginals & Unit-Collapse Decimation for Monotone 1-in-3 SAT.

Strictly single-pass decimation with ZERO recursive tree backtracking (capped at O(n)
deterministic polynomial restarts). Uses square-root-free LDL^T factorization from
primitives.py, BitLedger instrumentation from bitwidth.py, and independent verification
from verifier.py. Strictly isolated from generators.py and harness.py.
"""

from __future__ import annotations

from collections import deque
import math
import time
from typing import Any, Sequence

from ..bitwidth import (
    BitLedger,
    BitWidthExceededError,
    TrackedInt,
    TrackedScalar,
    make_scalar,
    t_acos,
    t_cos,
    t_fmod_2pi,
    t_pi,
    t_sin,
    t_sqrt,
)
from ..instance import Monotone1in3Instance, SparseIncidence, build_incidence
from ..primitives import (
    LDLTFactor,
    SparseOperators,
    build_M0,
    build_M_cert,
    clamp_scalar,
    greedy_conflict_round,
    is_finite_scalar,
    ldlt_factor,
    ldlt_solve,
    threshold_round,
    walsh_fourier_clause_eval,
)
from ..solver import SolverConfig, SolverResult
from ..verifier import VerificationResult, verify_assignment


# ---------------------------------------------------------------------------
# Deterministic 1-in-3 Unit-Collapse Propagator (O(n + m), zero recursion)
# ---------------------------------------------------------------------------


def unit_collapse_propagate(
    fixed: list[int | None],
    inc: SparseIncidence,
    seed_vars: Sequence[int] | None = None,
    ledger: BitLedger | None = None,
    conflict_clauses: list[int] | None = None,
) -> bool:
    """Propagate deterministic 1-in-3 unit-collapse deductions in-place.

    Rules for each clause sum(coeff_v * x_v) == 1:
    - If sum of fixed literals > 1 -> contradiction (return False).
    - If sum of fixed literals == 1 -> force all unfixed literals in clause to 0.
    - If sum of fixed literals == 0:
      - If 0 unfixed literals remain -> contradiction (return False).
      - If 1 unfixed literal (v, coeff) remains:
        - If coeff == 1 -> force x_v = 1.
        - Else (coeff >= 2) -> contradiction (return False).
    - Repeated variable with coeff == 3 -> immediate contradiction.
    - Repeated variable with coeff == 2 -> forces x_a = 0, x_b = 1.

    Returns True if consistent, False if a local contradiction is detected.
    """
    queue: deque[int] = deque()
    in_queue = [False] * inc.n_vars

    def _assign(v: int, val: int) -> bool:
        cur = fixed[v]
        if cur is not None:
            return cur == val
        fixed[v] = val
        if not in_queue[v]:
            in_queue[v] = True
            queue.append(v)
        return True

    def _check_clause(c_idx: int) -> bool:
        terms = inc.clause_terms[c_idx]
        sum_fixed = 0
        unfixed: list[tuple[int, int]] = []
        for v, coeff in terms:
            fv = fixed[v]
            if fv is not None:
                sum_fixed += coeff * fv
            else:
                if coeff == 3:
                    if conflict_clauses is not None:
                        conflict_clauses.append(c_idx)
                    return False
                if coeff == 2:
                    if not _assign(v, 0):
                        if conflict_clauses is not None:
                            conflict_clauses.append(c_idx)
                        return False
                else:
                    unfixed.append((v, coeff))

        if ledger is not None:
            ledger.record_int(sum_fixed, count_op=True)

        if sum_fixed > 1:
            if conflict_clauses is not None:
                conflict_clauses.append(c_idx)
            return False

        if sum_fixed == 1:
            for v, _ in unfixed:
                if not _assign(v, 0):
                    if conflict_clauses is not None:
                        conflict_clauses.append(c_idx)
                    return False
            return True

        # sum_fixed == 0
        if not unfixed:
            if conflict_clauses is not None:
                conflict_clauses.append(c_idx)
            return False
        if len(unfixed) == 1:
            v, coeff = unfixed[0]
            if coeff != 1:
                if conflict_clauses is not None:
                    conflict_clauses.append(c_idx)
                return False
            if not _assign(v, 1):
                if conflict_clauses is not None:
                    conflict_clauses.append(c_idx)
                return False
        return True

    if seed_vars is None:
        # Initial full sweep over all clauses to catch repeated literals and existing assignments
        for c_idx in range(inc.m_clauses):
            if not _check_clause(c_idx):
                return False
    else:
        for v in seed_vars:
            if not in_queue[v]:
                in_queue[v] = True
                queue.append(v)

    while queue:
        v = queue.popleft()
        in_queue[v] = False
        for c_idx, _ in inc.var_clauses[v]:
            if not _check_clause(c_idx):
                return False

    return True


def _root_failed_literal_propagation(
    root_fixed: list[int | None],
    inc: SparseIncidence,
    ledger: BitLedger,
    max_sweeps: int = 4,
    deadline: float | None = None,
) -> tuple[bool, bool]:
    """Sound root-only 1-step failed-literal propagation and backbone intersection.

    Operates strictly before any speculative choice.
    Returns (is_consistent, all_fixed).
    If is_consistent is False, the formula is 100% logically UNSAT.
    """
    n = inc.n_vars
    for _ in range(max_sweeps):
        if deadline is not None and time.perf_counter() >= deadline:
            break
        changed = False
        for i in range(n):
            if root_fixed[i] is not None:
                continue
            if deadline is not None and time.perf_counter() >= deadline:
                break

            f0 = list(root_fixed)
            f0[i] = 0
            ok0 = unit_collapse_propagate(f0, inc, seed_vars=(i,), ledger=ledger)

            f1 = list(root_fixed)
            f1[i] = 1
            ok1 = unit_collapse_propagate(f1, inc, seed_vars=(i,), ledger=ledger)

            if not ok0 and not ok1:
                return False, False
            if not ok0 and ok1:
                root_fixed[:] = f1
                changed = True
                continue
            if ok0 and not ok1:
                root_fixed[:] = f0
                changed = True
                continue

            # Both branches locally consistent: sound backbone intersection
            common_seeds: list[int] = []
            for j in range(n):
                if root_fixed[j] is None and f0[j] is not None and f0[j] == f1[j]:
                    root_fixed[j] = f0[j]
                    common_seeds.append(j)
            if common_seeds:
                if not unit_collapse_propagate(root_fixed, inc, seed_vars=common_seeds, ledger=ledger):
                    return False, False
                changed = True

        if not changed:
            break

    all_fixed = all(v is not None for v in root_fixed)
    return True, all_fixed


# ---------------------------------------------------------------------------
# LDL^T Dual Spectral Certificate Evaluator (Square-Root-Free)
# ---------------------------------------------------------------------------


def _evaluate_dual_certificate_ldlt(
    y_cert: Sequence[TrackedScalar],
    s_cert: Sequence[TrackedScalar],
    factor_cert: LDLTFactor,
    ops: SparseOperators,
    compute_grad_s: bool = True,
) -> tuple[
    TrackedScalar,
    list[TrackedScalar],
    list[TrackedScalar],
    list[TrackedScalar],
]:
    """Evaluate D_spec(y, s), x_dual(y, s), grad_y, and grad_s using LDL^T."""
    n = ops.n
    m = ops.m
    at_y = ops.apply_AT(y_cert)
    neg_half = make_scalar(-0.5, ops.ledger, mode=ops.mode, decimal_prec=ops.decimal_prec)
    neg_half_b: list[TrackedScalar] = []
    for i in range(n):
        bi = at_y[i] - ops.two * ops.degrees_s[i] - s_cert[i]
        neg_half_b.append(neg_half * bi)

    x_dual = ldlt_solve(factor_cert, neg_half_b)

    y_sum = ops.zero
    for yj in y_cert:
        y_sum = y_sum + yj

    quad_term = ops.zero
    for i in range(n):
        quad_term = quad_term + x_dual[i] * neg_half_b[i]

    m_scalar = make_scalar(m, ops.ledger, mode=ops.mode, decimal_prec=ops.decimal_prec)
    d_spec = m_scalar - y_sum - quad_term

    ax_dual = ops.apply_A(x_dual)
    grad_y = [ax_dual[j] - ops.one for j in range(m)]
    grad_s = [x_dual[i] * x_dual[i] - x_dual[i] for i in range(n)] if compute_grad_s else []
    return d_spec, x_dual, grad_y, grad_s


def _compute_primal_metrics(
    x_vals: Sequence[TrackedScalar],
    r_vals: Sequence[TrackedScalar],
    ops: SparseOperators,
    inv_sqrt_m: TrackedScalar,
) -> tuple[TrackedScalar, TrackedScalar, TrackedScalar]:
    """Return (primal_res_inf, primal_res_l2, integrality_gap) via BitLedger."""
    zero = ops.zero
    one = ops.one
    if not r_vals:
        res_inf = zero
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
            res_l2 = t_sqrt(r2_sq) * inv_sqrt_m
        else:
            res_l2 = r2_sq

    igap = zero
    for xi in x_vals:
        d0 = abs(xi)
        d1 = abs(one - xi)
        gap_i = d0 if d0 <= d1 else d1
        if gap_i > igap:
            igap = gap_i
    return res_inf, res_l2, igap


def _greedy_round_with_fixed(
    x_vals: Sequence[TrackedScalar],
    fixed: Sequence[int | None],
    inc: SparseIncidence,
    ledger: BitLedger,
) -> list[int]:
    """Conflict-aware greedy rounding respecting already-fixed variables."""
    n = inc.n_vars
    m = inc.m_clauses
    x_hat = [0] * n
    clause_hits = [0] * m
    for i in range(n):
        if fixed[i] == 1:
            x_hat[i] = 1
            for c_idx, coeff in inc.var_clauses[i]:
                clause_hits[c_idx] += coeff

    unfixed_order = sorted(
        (i for i in range(n) if fixed[i] is None),
        key=lambda i: (-x_vals[i].value, i),
    )
    for i in unfixed_order:
        can_set = True
        for c_idx, coeff in inc.var_clauses[i]:
            if coeff > 1 or clause_hits[c_idx] > 0:
                can_set = False
                break
        if can_set:
            x_hat[i] = 1
            for c_idx, coeff in inc.var_clauses[i]:
                clause_hits[c_idx] += coeff
                ledger.record_int(clause_hits[c_idx], count_op=True)
    return x_hat


def _threshold_round_with_fixed(
    x_vals: Sequence[TrackedScalar],
    fixed: Sequence[int | None],
) -> list[int]:
    """Threshold rounding respecting already-fixed variables."""
    out: list[int] = []
    for i, xi in enumerate(x_vals):
        fi = fixed[i]
        if fi is not None:
            out.append(fi)
        else:
            out.append(1 if xi >= 0.5 else 0)
    return out


# ---------------------------------------------------------------------------
# Track D Main Solver
# ---------------------------------------------------------------------------


def solve_track_d(
    instance: Monotone1in3Instance,
    config: SolverConfig | None = None,
) -> SolverResult:
    """Solve Monotone 1-in-3 SAT via Single-Pass Primal-Dual Marginals & Unit-Collapse Decimation."""
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
    deadline = (t_start + cfg.max_time_sec) if cfg.max_time_sec is not None else None

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

    b_s_eff_float = cfg.B_s
    total_iters = 0
    best_d_spec = -math.inf
    best_candidate: tuple[int, ...] | None = None
    best_violations = m + 1
    last_res_inf = 1.0
    last_res_l2 = 1.0
    last_igap = 0.5
    last_dual_res = 0.0
    last_x_floats: tuple[float, ...] = tuple(1.0 / 3.0 for _ in range(n))
    iter_history: list[dict[str, Any]] = []

    try:
        inc = build_incidence(instance)
        ops = SparseOperators(inc, ledger, mode=mode, decimal_prec=dprec)

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
        beta_pin = make_scalar(0.30, ledger, mode=mode, decimal_prec=dprec)
        eta_spec = make_scalar(cfg.eta_spec, ledger, mode=mode, decimal_prec=dprec)
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

        omega_1 = pi_s / ops.three
        omega_2 = pi_s * half

        def _make_sat_result(
            assign: Sequence[int],
            ver: VerificationResult,
            reason: str,
        ) -> SolverResult:
            return SolverResult(
                status="SAT",
                assignment=tuple(assign),
                dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else 0.0,
                iterations=total_iters,
                runtime_sec=time.perf_counter() - t_start,
                primal_res_inf=0.0,
                primal_res_l2=0.0,
                integrality_gap=0.0,
                dual_residual=last_dual_res,
                clause_violation_count=0,
                bit_summary=ledger.summary(),
                iteration_history=iter_history,
                verification=ver,
                best_candidate=tuple(assign),
                termination_reason=reason,
                final_x=tuple(float(v) for v in assign),
                max_kappa2_cert_bound=kappa2_bound,
            )

        def _make_unsat_result(cert_val: float, reason: str) -> SolverResult:
            return SolverResult(
                status="UNSAT_CERTIFIED",
                assignment=None,
                dual_certificate_value=cert_val,
                iterations=total_iters,
                runtime_sec=time.perf_counter() - t_start,
                primal_res_inf=last_res_inf,
                primal_res_l2=last_res_l2,
                integrality_gap=last_igap,
                dual_residual=last_dual_res,
                clause_violation_count=best_violations if best_violations <= m else m,
                bit_summary=ledger.summary(),
                iteration_history=iter_history,
                verification=None,
                best_candidate=best_candidate,
                termination_reason=reason,
                final_x=last_x_floats,
                max_kappa2_cert_bound=kappa2_bound,
            )

        def _make_overflow_result() -> SolverResult:
            return SolverResult(
                status="OVERFLOW",
                assignment=None,
                dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                iterations=total_iters,
                runtime_sec=time.perf_counter() - t_start,
                primal_res_inf=last_res_inf,
                primal_res_l2=last_res_l2,
                integrality_gap=last_igap,
                dual_residual=last_dual_res,
                clause_violation_count=best_violations if best_violations <= m else m,
                bit_summary=ledger.summary(),
                iteration_history=iter_history,
                verification=None,
                best_candidate=best_candidate,
                termination_reason="OVERFLOW",
                final_x=last_x_floats,
                max_kappa2_cert_bound=kappa2_bound,
            )

        # ------------------------------------------------------------------
        # Stage 1: Deterministic Root Unit-Collapse & 1-Step Failed-Literal
        # (Strictly before any speculative choice -> 100% sound UNSAT)
        # ------------------------------------------------------------------
        root_fixed: list[int | None] = [None] * n
        if not unit_collapse_propagate(root_fixed, inc, seed_vars=None, ledger=ledger):
            return _make_unsat_result(float(m), "ROOT_UNIT_COLLAPSE_UNSAT")

        ok_root, all_fixed_root = _root_failed_literal_propagation(
            root_fixed, inc, ledger=ledger, max_sweeps=4, deadline=deadline
        )
        if not ok_root:
            return _make_unsat_result(1.0, "ROOT_FAILED_LITERAL_UNSAT")

        if all_fixed_root:
            cand = [int(v) for v in root_fixed]  # type: ignore[arg-type]
            ver = verify_assignment(instance, cand)
            if ver.is_sat:
                return _make_sat_result(cand, ver, "ROOT_PROPAGATION_SAT")
            return _make_unsat_result(1.0, "ROOT_PROPAGATION_UNSAT")

        # ------------------------------------------------------------------
        # Stage 2: Square-Root-Free LDL^T Preconditioner & Root Dual Certificate
        # ------------------------------------------------------------------
        M0 = build_M0(ops, eta_0)
        L0_ldlt = ldlt_factor(M0, ledger, mode=mode, decimal_prec=dprec)
        if L0_ldlt is None:
            raise RuntimeError("Unexpected non-SPD M_0 in LDL^T")

        # Root dual certificate state (evaluated ONLY on original root instance)
        y_cert = [zero] * m
        s_cert = [
            clamp_scalar(ops.degrees_s[i] + two_eps_chol, B_s_eff)
            for i in range(n)
        ]
        L_cert: LDLTFactor | None = ldlt_factor(
            build_M_cert(ops, s_cert), ledger, mode=mode, decimal_prec=dprec
        )
        cert_pd_verified = (
            ldlt_factor(
                build_M_cert(ops, s_cert, shift_diag=eps_chol),
                ledger,
                mode=mode,
                decimal_prec=dprec,
            )
            is not None
        )

        # Short root dual certificate ascent burst (catches rank-1 / quadratic UNSAT cores)
        cert_burst = min(15, max(4, n // 3))
        if cfg.max_iters is not None:
            cert_burst = min(cert_burst, max(1, cfg.max_iters))
        if L_cert is not None:
            for c_step in range(cert_burst):
                if deadline is not None and time.perf_counter() >= deadline:
                    break
                do_s = (c_step > 0) and (c_step % max(1, cert_burst // 2) == 0)
                d_spec, x_dual, grad_y, grad_s = _evaluate_dual_certificate_ldlt(
                    y_cert, s_cert, L_cert, ops, compute_grad_s=do_s
                )
                d_spec_float = float(d_spec)
                if math.isfinite(d_spec_float) and d_spec_float > best_d_spec:
                    best_d_spec = d_spec_float

                x_dual_norm_sq_s = zero
                for xi_d in x_dual:
                    x_dual_norm_sq_s = x_dual_norm_sq_s + xi_d * xi_d
                eps_cert_s = eps_cert_floor_s + cert_tol_coeff_s * x_dual_norm_sq_s

                if cert_pd_verified and is_finite_scalar(d_spec) and d_spec > eps_cert_s:
                    return _make_unsat_result(d_spec_float, "UNSAT_CERT_LDLT")

                y_cert = [
                    clamp_scalar(y_cert[j] + alpha_y * grad_y[j], B_y)
                    for j in range(m)
                ]
                if do_s:
                    step_s = alpha_s_s
                    for _ in range(min(4, cfg.k_bt)):
                        s_cand: list[TrackedScalar] = []
                        for i in range(n):
                            sc = clamp_scalar(s_cert[i] + step_s * grad_s[i], B_s_eff)
                            if inc.degrees[i] == 0 and sc < two_eps_chol:
                                sc = two_eps_chol
                            s_cand.append(sc)
                        if (
                            ldlt_factor(
                                build_M_cert(ops, s_cand, shift_diag=eps_chol),
                                ledger,
                                mode=mode,
                                decimal_prec=dprec,
                            )
                            is not None
                        ):
                            new_fac = ldlt_factor(
                                build_M_cert(ops, s_cand),
                                ledger,
                                mode=mode,
                                decimal_prec=dprec,
                            )
                            if new_fac is not None:
                                s_cert = s_cand
                                L_cert = new_fac
                                cert_pd_verified = True
                                break
                        step_s = step_s * half

                if ledger.nan_count > 0 or ledger.overflow_count > 0 or ledger.guardrail_tripped:
                    return _make_overflow_result()

        # ------------------------------------------------------------------
        # Stage 3: Single-Pass Primal-Dual Marginal Decimation Loop
        # Strictly capped at O(n) restarts (<= min(n, 20)), ZERO backtracking
        # ------------------------------------------------------------------
        max_restarts = min(n, 20)
        max_total_iters = cfg.max_iters if cfg.max_iters is not None else max(60, 8 * n)

        one_third = one / ops.three
        phi_base = t_acos(one_third)
        n_plus_1 = make_scalar(n + 1, ledger, mode=mode, decimal_prec=dprec)

        # Clause conflict frequency across restarts (dual-weighted perturbation)
        clause_conflict_counts = [0] * m

        for r_idx in range(max_restarts):
            if total_iters >= max_total_iters:
                break
            if deadline is not None and time.perf_counter() >= deadline:
                break

            fixed = list(root_fixed)

            # Initialize torus phases with deterministic restart-specific rotation
            phi: list[TrackedScalar] = []
            freq_mult = 1 + 2 * r_idx
            phase_shift = r_idx * 7
            delta_r = make_scalar(
                cfg.delta_0 * (1.0 + 0.15 * (r_idx % 5)),
                ledger,
                mode=mode,
                decimal_prec=dprec,
            )
            for i in range(n):
                fi = fixed[i]
                if fi == 0:
                    phi.append(zero)
                elif fi == 1:
                    phi.append(pi_s)
                else:
                    idx_val = ((i + 1) * freq_mult + phase_shift) % (n + 1) + 1
                    idx_s = make_scalar(idx_val, ledger, mode=mode, decimal_prec=dprec)
                    ang = (two_pi_s * idx_s) / n_plus_1
                    phi.append(t_fmod_2pi(phi_base + delta_r * t_sin(ang), mode=mode, decimal_prec=dprec))

            p = [zero] * n
            # Initialize dual multipliers lam with conflict-clause weighting from prior restarts
            lam: list[TrackedScalar] = []
            for j in range(m):
                cc = clause_conflict_counts[j]
                if cc > 0:
                    sign_j = 1.0 if ((j + r_idx) % 2 == 0) else -1.0
                    lam_init = make_scalar(
                        sign_j * min(2.0, 0.25 * cc),
                        ledger,
                        mode=mode,
                        decimal_prec=dprec,
                    )
                    lam.append(clamp_scalar(lam_init, B_lambda))
                else:
                    lam.append(zero)

            x_prev: list[TrackedScalar] | None = None
            decimation_step = 0
            pass_conflict_clauses: list[int] = []

            # Single-pass decimation loop: each iteration fixes >= 1 variable (no backtracking!)
            while decimation_step < n:
                if total_iters >= max_total_iters:
                    break
                if deadline is not None and time.perf_counter() >= deadline:
                    break

                unfixed_vars = [i for i in range(n) if fixed[i] is None]
                if not unfixed_vars:
                    cand = [int(v) for v in fixed]  # type: ignore[arg-type]
                    ver = verify_assignment(instance, cand)
                    if ver.is_sat:
                        return _make_sat_result(cand, ver, "DECIMATION_SAT")
                    break

                # Short primal-dual burst on the active subproblem
                if decimation_step == 0:
                    burst_len = 10 if r_idx == 0 else 6
                else:
                    burst_len = 3
                burst_len = min(burst_len, max_total_iters - total_iters)
                if burst_len <= 0:
                    break

                x: list[TrackedScalar] = [one_third] * n
                g_x: list[TrackedScalar] = [zero] * n

                for _b in range(burst_len):
                    if deadline is not None and time.perf_counter() >= deadline:
                        break

                    ledger.begin_iteration(total_iters)

                    # 1. Manifold evaluation (respecting fixed variables)
                    sin_phi: list[TrackedScalar] = []
                    sigma: list[TrackedScalar] = []
                    x = []
                    for i in range(n):
                        fi = fixed[i]
                        if fi == 0:
                            sin_phi.append(zero)
                            sigma.append(one)
                            x.append(zero)
                        elif fi == 1:
                            sin_phi.append(zero)
                            sigma.append(-one)
                            x.append(one)
                        else:
                            sp = t_sin(phi[i])
                            sg = t_cos(phi[i])
                            sin_phi.append(sp)
                            sigma.append(sg)
                            x.append((one - sg) * half)

                    last_x_floats = tuple(float(xi) for xi in x)
                    ax = ops.apply_A(x)
                    r = [ax[j] - one for j in range(m)]
                    w = [one + kappa_w * (rj * rj) for rj in r]

                    res_inf_s, res_l2_s, igap_s = _compute_primal_metrics(x, r, ops, inv_sqrt_m_s)
                    last_res_inf = float(res_inf_s)
                    last_res_l2 = float(res_l2_s)
                    last_igap = float(igap_s)

                    if not (is_finite_scalar(res_inf_s) and is_finite_scalar(res_l2_s)):
                        ledger.end_iteration()
                        return _make_overflow_result()

                    # Check rounding + independent verifier
                    cand_thr = _threshold_round_with_fixed(x, fixed)
                    ver_thr = verify_assignment(instance, cand_thr)
                    if ver_thr.is_sat:
                        total_iters += 1
                        ledger.end_iteration()
                        return _make_sat_result(cand_thr, ver_thr, "SAT_FOUND_THRESHOLD")

                    cand_greedy = _greedy_round_with_fixed(x, fixed, inc, ledger)
                    ver_greedy = verify_assignment(instance, cand_greedy)
                    if ver_greedy.is_sat:
                        total_iters += 1
                        ledger.end_iteration()
                        return _make_sat_result(cand_greedy, ver_greedy, "SAT_FOUND_GREEDY")

                    for cand_c, ver_c in ((cand_thr, ver_thr), (cand_greedy, ver_greedy)):
                        vcount = len(ver_c.violated_clauses)
                        if vcount < best_violations:
                            best_violations = vcount
                            best_candidate = tuple(cand_c)

                    # 2. Primal-dual x-gradient (dual sensitivity)
                    clause_drive: list[TrackedScalar] = []
                    for j in range(m):
                        rj = r[j]
                        beat_j = (t_sin(omega_1 * rj) / omega_1) + (t_sin(omega_2 * rj) / omega_2)
                        clause_drive.append((w[j] + rho) * rj + lam[j] + gamma_beat * beat_j)

                    gx_lin = ops.apply_AT(clause_drive)
                    kx = ops.apply_K(x)
                    g_x = [gx_lin[i] + alpha_k * kx[i] for i in range(n)]

                    # 3. Walsh-Fourier harmonic + Boolean pinning + Fisher-Rao pullback
                    _, grad_wf = walsh_fourier_clause_eval(phi, sin_phi, sigma, w, ops)
                    g_phi: list[TrackedScalar] = []
                    for i in range(n):
                        if fixed[i] is not None:
                            g_phi.append(zero)
                        else:
                            s_i = sin_phi[i]
                            pb = half * s_i * g_x[i]
                            pin = beta_pin * s_i * sigma[i]
                            g_phi.append(pb + gamma_wf * grad_wf[i] + pin)

                    # 4. LDL^T preconditioned & spectrally filtered descent direction
                    f_g = ops.apply_F_spec(g_phi, eta_spec)
                    m0_inv_fg = ldlt_solve(L0_ldlt, f_g)
                    g_tilde = ops.apply_F_spec(m0_inv_fg, eta_spec)

                    # 5. Geodesic torus update & over-relaxed PDHG multiplier update
                    p_next: list[TrackedScalar] = []
                    phi_next: list[TrackedScalar] = []
                    for i in range(n):
                        if fixed[i] is not None:
                            p_next.append(zero)
                            phi_next.append(zero if fixed[i] == 0 else pi_s)
                        else:
                            pi_new = mu_damp * p[i] - tau_step * g_tilde[i]
                            p_next.append(pi_new)
                            phi_next.append(
                                t_fmod_2pi(phi[i] + pi_new, mode=mode, decimal_prec=dprec)
                            )

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
                    last_dual_res = float(dual_res_s)

                    p = p_next
                    phi = phi_next
                    x_prev = x
                    lam = lam_next

                    bit_snap = ledger.end_iteration()
                    if cfg.record_iter_history:
                        iter_history.append({
                            "iteration": total_iters,
                            "restart": r_idx,
                            "decimation_step": decimation_step,
                            "primal_res_inf": last_res_inf,
                            "primal_res_l2": last_res_l2,
                            "integrality_gap": last_igap,
                            **bit_snap,
                        })
                    total_iters += 1

                    if ledger.nan_count > 0 or ledger.overflow_count > 0 or ledger.guardrail_tripped:
                        return _make_overflow_result()

                # ----------------------------------------------------------
                # Decimation Step: 1-step unit-collapse lookahead + confidence
                # ----------------------------------------------------------
                # Compute active clause degree (extra weight for 2-literal clauses)
                active_deg = [0] * n
                for c_idx in range(m):
                    terms = inc.clause_terms[c_idx]
                    sat_already = False
                    c_unfixed: list[int] = []
                    for v, _ in terms:
                        fv = fixed[v]
                        if fv == 1:
                            sat_already = True
                            break
                        if fv is None:
                            c_unfixed.append(v)
                    if not sat_already and c_unfixed:
                        w_deg = 2 if len(c_unfixed) == 2 else 1
                        for v in c_unfixed:
                            active_deg[v] += w_deg

                max_gx = 0.0
                for i in unfixed_vars:
                    ag = abs(float(g_x[i]))
                    if ag > max_gx:
                        max_gx = ag
                gx_scale = 1.0 + max_gx

                base_fixed_cnt = n - len(unfixed_vars)
                forced_commit: list[int | None] | None = None
                pass_contradiction = False
                best_var = -1
                best_score = -1.0
                best_branch_fixed: list[int | None] | None = None

                # Deterministic restart-dependent weighting of confidence factors
                w_dual = 0.25 if (r_idx % 3 == 0) else (0.50 if (r_idx % 3 == 1) else 0.15)
                w_casc = 0.25 if (r_idx % 2 == 0) else 0.45

                for i in unfixed_vars:
                    f0 = list(fixed)
                    f0[i] = 0
                    ok0 = unit_collapse_propagate(
                        f0, inc, seed_vars=(i,), ledger=ledger, conflict_clauses=pass_conflict_clauses
                    )

                    f1 = list(fixed)
                    f1[i] = 1
                    ok1 = unit_collapse_propagate(
                        f1, inc, seed_vars=(i,), ledger=ledger, conflict_clauses=pass_conflict_clauses
                    )

                    if not ok0 and not ok1:
                        # Contradiction after speculative clamp -> abort pass, restart
                        pass_contradiction = True
                        break
                    if not ok0 and ok1:
                        # Sound 1-step failed-literal deduction within this pass
                        forced_commit = f1
                        break
                    if ok0 and not ok1:
                        forced_commit = f0
                        break

                    # Both values locally consistent: compute primal-dual confidence
                    xi_val = float(x[i])
                    bias = abs(2.0 * xi_val - 1.0)
                    gx_i = float(g_x[i])
                    dual_sens = abs(gx_i) / gx_scale

                    if abs(xi_val - 0.5) >= 1e-6:
                        pref = 1 if xi_val >= 0.5 else 0
                    else:
                        pref = 1 if gx_i < 0.0 else 0

                    # On later restarts, allow deterministic phase-tie exploration
                    if r_idx >= 3 and bias < 0.15 and ((i + r_idx) % 4 == 0):
                        pref = 1 - pref

                    chosen_f = f1 if pref == 1 else f0
                    cascade = sum(1 for v in chosen_f if v is not None) - base_fixed_cnt
                    score = (bias + w_dual * dual_sens + 0.05) * (
                        1.0 + 0.12 * active_deg[i] + w_casc * math.log2(1.0 + max(1, cascade))
                    )
                    if score > best_score:
                        best_score = score
                        best_var = i
                        best_branch_fixed = chosen_f

                if pass_contradiction:
                    for c_idx in pass_conflict_clauses:
                        clause_conflict_counts[c_idx] += 1
                    break

                if forced_commit is not None:
                    fixed = forced_commit
                elif best_var >= 0 and best_branch_fixed is not None:
                    fixed = best_branch_fixed
                else:
                    break

                # Sync phi and p for newly fixed variables
                for i in range(n):
                    fi = fixed[i]
                    if fi is not None:
                        phi[i] = zero if fi == 0 else pi_s
                        p[i] = zero

                decimation_step += 1

                # Immediate check if all variables are now fixed
                if all(v is not None for v in fixed):
                    cand = [int(v) for v in fixed]  # type: ignore[arg-type]
                    ver = verify_assignment(instance, cand)
                    if ver.is_sat:
                        return _make_sat_result(cand, ver, "DECIMATION_SAT")
                    vcount = len(ver.violated_clauses)
                    if vcount < best_violations:
                        best_violations = vcount
                        best_candidate = tuple(cand)
                    for c_idx, _, _ in ver.violated_clauses:
                        clause_conflict_counts[c_idx] += 1
                    break

        reason = "TIMEOUT" if (deadline is not None and time.perf_counter() >= deadline) else "MAX_RESTARTS"
        return SolverResult(
            status="UNRESOLVED",
            assignment=None,
            dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
            iterations=total_iters,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=last_res_inf,
            primal_res_l2=last_res_l2,
            integrality_gap=last_igap,
            dual_residual=last_dual_res,
            clause_violation_count=best_violations if best_violations <= m else m,
            bit_summary=ledger.summary(),
            iteration_history=iter_history,
            verification=None,
            best_candidate=best_candidate,
            termination_reason=reason,
            final_x=last_x_floats,
            max_kappa2_cert_bound=kappa2_bound,
        )

    except BitWidthExceededError:
        return SolverResult(
            status="OVERFLOW",
            assignment=None,
            dual_certificate_value=-math.inf,
            iterations=total_iters,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=math.inf,
            primal_res_l2=math.inf,
            integrality_gap=1.0,
            dual_residual=math.inf,
            clause_violation_count=m,
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=None,
            best_candidate=best_candidate,
            termination_reason="OVERFLOW",
            final_x=(),
            max_kappa2_cert_bound=(18.0 * m + b_s_eff_float) / cfg.eps_chol,
        )
