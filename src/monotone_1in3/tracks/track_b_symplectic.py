"""Track B: Symplectic Störmer-Verlet Integrator + Polyrhythmic Phase-Kick Annealing.

Strictly isolated from generators.py, harness.py, and any external SAT/CSP/ILP solvers.
Every candidate SAT assignment MUST pass the independent deterministic verifier.
Uses square-root-free LDL^T factorization from primitives.py and instruments integer
and float telemetry via BitLedger from bitwidth.py.
"""

from __future__ import annotations

import math
import time
from typing import Any, Sequence

from ..bitwidth import BitLedger, BitWidthExceededError, TrackedScalar, make_scalar
from ..instance import Monotone1in3Instance, SparseIncidence, build_incidence
from ..primitives import LDLTFactor, ldlt_factor, ldlt_solve
from ..solver import SolverConfig, SolverResult
from ..verifier import verify_assignment

_TWO_PI = 2.0 * math.pi
_OMEGA_1 = math.pi / 3.0
_OMEGA_2 = math.pi / 5.0
_OMEGA_3 = math.pi / 7.0
_OMEGA_GOLD = math.pi * (math.sqrt(5.0) - 1.0) * 0.5
_EPS_MACH = 2.0**-53
_MOMENTUM_FLUSH = 1e-12
_MOMENTUM_CLAMP = 14.0
_WEIGHT_MIN = 1.0
_WEIGHT_MAX = 24.0


def _walsh_sign(a: int, b: int) -> float:
    """Deterministic Walsh-Hadamard character (-1)^popcount(a & b) in {-1.0, +1.0}."""
    return -1.0 if ((a & b).bit_count() & 1) else 1.0


def _extract_ldlt_raw(
    fac: LDLTFactor,
) -> tuple[tuple[tuple[tuple[int, float], ...], ...], tuple[float, ...]]:
    """Extract raw float64 (offdiag_nz, D_inv) from a verified LDLTFactor."""
    offdiag_raw = tuple(
        tuple((col, float(val.value)) for col, val in row)
        for row in fac.offdiag_nz
    )
    d_inv_raw = tuple(1.0 / float(d.value) for d in fac.D)
    return offdiag_raw, d_inv_raw


def _ldlt_solve_raw(
    offdiag_raw: tuple[tuple[tuple[int, float], ...], ...],
    d_inv_raw: tuple[float, ...],
    rhs: Sequence[float],
) -> list[float]:
    """Fast pure-float64 triangular solve (L D L^T) x = rhs from a verified LDLTFactor."""
    n = len(d_inv_raw)
    if n == 0:
        return []
    y = list(rhs)
    for i in range(n):
        s = y[i]
        for j, l_ij in offdiag_raw[i]:
            s -= l_ij * y[j]
        y[i] = s

    x = [y[i] * d_inv_raw[i] for i in range(n)]
    for j in range(n - 1, -1, -1):
        xj = x[j]
        if xj != 0.0:
            for k, l_jk in offdiag_raw[j]:
                x[k] -= l_jk * xj
    return x


def _ldlt_diag_margins_raw(
    offdiag_raw: tuple[tuple[tuple[int, float], ...], ...],
    d_inv_raw: tuple[float, ...],
) -> list[float]:
    """Compute exact single-coordinate PD margins mu_i = 1 / ((L D L^T)^{-1})_{ii} without sqrt."""
    n = len(d_inv_raw)
    margins = [0.0] * n
    for i in range(n):
        u = [0.0] * n
        u[i] = 1.0
        w = d_inv_raw[i]
        for r in range(i + 1, n):
            s = 0.0
            for k, l_rk in offdiag_raw[r]:
                if k >= i:
                    s += l_rk * u[k]
            ur = -s
            u[r] = ur
            if ur != 0.0:
                w += (ur * ur) * d_inv_raw[r]
        margins[i] = 1.0 / w if w > 0.0 else 0.0
    return margins


def _ldlt_is_spd_raw(
    ata_int: Sequence[Sequence[int]],
    degrees: Sequence[int],
    s_cert: Sequence[float],
    shift_diag: float,
) -> tuple[bool, tuple[tuple[tuple[int, float], ...], ...], tuple[float, ...]]:
    """Fast raw float64 square-root-free LDL^T SPD screen for M_cert(s) - shift_diag * I."""
    n = len(degrees)
    L = [[0.0] * n for _ in range(n)]
    D = [0.0] * n
    offdiag: list[tuple[tuple[int, float], ...]] = []
    for i in range(n):
        row_L = L[i]
        ata_row = ata_int[i]
        nz_list: list[tuple[int, float]] = []
        for j in range(i):
            s = 2.0 * ata_row[j]
            for k, ljk in offdiag[j]:
                lik = row_L[k]
                if lik != 0.0:
                    s -= (lik * D[k]) * ljk
            val = s / D[j]
            if not math.isfinite(val):
                return False, (), ()
            row_L[j] = val
            if val != 0.0:
                nz_list.append((j, val))
        diag_s = 2.0 * ata_row[i] + s_cert[i] - degrees[i] - shift_diag
        for j, lij in nz_list:
            diag_s -= (lij * lij) * D[j]
        if not math.isfinite(diag_s) or diag_s <= 0.0:
            return False, (), ()
        row_L[i] = 1.0
        D[i] = diag_s
        offdiag.append(tuple(nz_list))
    return True, tuple(offdiag), tuple(1.0 / d for d in D)


def _build_m0_tracked(
    ata_int: Sequence[Sequence[int]],
    eta_0: float,
    ledger: BitLedger,
) -> list[list[TrackedScalar]]:
    """Construct M_0 = I + eta_0 A^T A as TrackedFloat for primitives.ldlt_factor."""
    n = len(ata_int)
    mat: list[list[TrackedScalar]] = []
    for i in range(n):
        ata_row = ata_int[i]
        row: list[TrackedScalar] = []
        for j in range(n):
            val = eta_0 * float(ata_row[j])
            if i == j:
                val += 1.0
            row.append(make_scalar(val, ledger, mode="float64"))
        mat.append(row)
    return mat


def _build_m_cert_tracked(
    ata_int: Sequence[Sequence[int]],
    degrees: Sequence[int],
    s_cert: Sequence[float],
    ledger: BitLedger,
    shift_diag: float = 0.0,
) -> list[list[TrackedScalar]]:
    """Construct M_cert(s) = 2 A^T A - diag(d) + diag(s) - shift_diag * I."""
    n = len(ata_int)
    mat: list[list[TrackedScalar]] = []
    for i in range(n):
        ata_row = ata_int[i]
        row: list[TrackedScalar] = []
        for j in range(n):
            val = 2.0 * float(ata_row[j])
            if i == j:
                val += s_cert[i] - float(degrees[i]) - shift_diag
            row.append(make_scalar(val, ledger, mode="float64"))
        mat.append(row)
    return mat


def _eval_dual_raw(
    y_cert: Sequence[float],
    s_cert: Sequence[float],
    offdiag_cert: tuple[tuple[tuple[int, float], ...], ...],
    d_inv_cert: tuple[float, ...],
    inc: SparseIncidence,
) -> tuple[float, list[float], list[float], list[float]]:
    """Fast raw float64 evaluation of D_spec(y, s), x_dual, grad_y, grad_s."""
    n = inc.n_vars
    m = inc.m_clauses
    var_clauses = inc.var_clauses
    degrees = inc.degrees

    neg_half_b = [0.0] * n
    for i in range(n):
        at_yi = 0.0
        for c_idx, coeff in var_clauses[i]:
            at_yi += coeff * y_cert[c_idx]
        bi = at_yi - 2.0 * degrees[i] - s_cert[i]
        neg_half_b[i] = -0.5 * bi

    x_dual = _ldlt_solve_raw(offdiag_cert, d_inv_cert, neg_half_b)

    y_sum = 0.0
    for yj in y_cert:
        y_sum += yj
    quad = 0.0
    for i in range(n):
        quad += x_dual[i] * neg_half_b[i]
    d_spec = float(m) - y_sum - quad

    grad_y = [0.0] * m
    for j, (a, b, c) in enumerate(inc.clauses):
        grad_y[j] = x_dual[a] + x_dual[b] + x_dual[c] - 1.0

    grad_s = [xi * xi - xi for xi in x_dual]
    return d_spec, x_dual, grad_y, grad_s


def _verify_dual_certificate_ldlt(
    y_cert: Sequence[float],
    s_cert: Sequence[float],
    ata_int: Sequence[Sequence[int]],
    inc: SparseIncidence,
    eps_chol: float,
    kappa2_bound: float,
    ledger: BitLedger,
) -> tuple[bool, float]:
    """Sound LDL^T verification of D_spec(y, s) > eps_cert via primitives.ldlt_factor/solve."""
    n = inc.n_vars
    m = inc.m_clauses
    m_shifted = _build_m_cert_tracked(ata_int, inc.degrees, s_cert, ledger, shift_diag=eps_chol)
    if ldlt_factor(m_shifted, ledger, mode="float64") is None:
        return False, -math.inf

    m_full = _build_m_cert_tracked(ata_int, inc.degrees, s_cert, ledger, shift_diag=0.0)
    fac_full = ldlt_factor(m_full, ledger, mode="float64")
    if fac_full is None:
        return False, -math.inf

    neg_half_b_s: list[TrackedScalar] = []
    for i in range(n):
        at_yi = 0.0
        for c_idx, coeff in inc.var_clauses[i]:
            at_yi += coeff * y_cert[c_idx]
        bi = at_yi - 2.0 * inc.degrees[i] - s_cert[i]
        neg_half_b_s.append(make_scalar(-0.5 * bi, ledger, mode="float64"))

    x_dual_s = ldlt_solve(fac_full, neg_half_b_s)
    y_sum = sum(y_cert)
    quad = 0.0
    x_norm_sq = 0.0
    for i in range(n):
        xi = float(x_dual_s[i].value)
        if not math.isfinite(xi):
            return False, -math.inf
        quad += xi * float(neg_half_b_s[i].value)
        x_norm_sq += xi * xi

    d_spec = float(m) - y_sum - quad
    ledger.record_float(d_spec, count_op=True)
    eps_cert = 1e-6 + (n * n) * _EPS_MACH * kappa2_bound * x_norm_sq
    if math.isfinite(d_spec) and d_spec > eps_cert:
        return True, d_spec
    return False, d_spec


def _greedy_conflict_round_fast(x: Sequence[float], inc: SparseIncidence) -> list[int]:
    """Conflict-aware greedy sweep rounding in descending order of x_i."""
    n = inc.n_vars
    m = inc.m_clauses
    order = sorted(range(n), key=lambda i: (-x[i], i))
    x_hat = [0] * n
    clause_hits = [0] * m
    var_clauses = inc.var_clauses
    for i in order:
        can_set = True
        for c_idx, coeff in var_clauses[i]:
            if coeff > 1 or clause_hits[c_idx] > 0:
                can_set = False
                break
        if can_set:
            x_hat[i] = 1
            for c_idx, coeff in var_clauses[i]:
                clause_hits[c_idx] += coeff
    return x_hat


def _deterministic_1flip_polish(
    assign_in: Sequence[int],
    x_cont: Sequence[float],
    clause_weights: Sequence[float],
    inc: SparseIncidence,
    max_steps: int,
) -> tuple[list[int], int, list[int]]:
    """Deterministic local 1-flip polish with zero recursive backtracking.

    Strictly reduces violation count (with bounded weighted-tie plateau moves on distinct
    variables). Returns (polished_assign, violation_count, violated_clause_indices).
    """
    n = inc.n_vars
    m = inc.m_clauses
    clauses = inc.clauses
    var_clauses = inc.var_clauses
    assign = list(assign_in)

    clause_sum = [0] * m
    viol_count = 0
    for j, (a, b, c) in enumerate(clauses):
        s = assign[a] + assign[b] + assign[c]
        clause_sum[j] = s
        if s != 1:
            viol_count += 1

    if viol_count == 0:
        return assign, 0, []

    plateau_used = 0
    max_plateau = max(4, n // 4)
    plateau_flipped: set[int] = set()

    for _ in range(max_steps):
        if viol_count == 0:
            break

        # Collect distinct candidate variables in currently violated clauses
        cand_vars_set: set[int] = set()
        for j in range(m):
            if clause_sum[j] != 1:
                a, b, c = clauses[j]
                cand_vars_set.add(a)
                cand_vars_set.add(b)
                cand_vars_set.add(c)

        best_var = -1
        best_dv = 1  # want < 0, or == 0 with strict weighted improvement
        best_dw = 0.0
        best_align = -1e9

        for v in sorted(cand_vars_set):
            cur = assign[v]
            delta_x = 1 if cur == 0 else -1
            dv = 0
            dw = 0.0
            for c_idx, coeff in var_clauses[v]:
                old_s = clause_sum[c_idx]
                new_s = old_s + delta_x * coeff
                old_bad = 1 if old_s != 1 else 0
                new_bad = 1 if new_s != 1 else 0
                diff = new_bad - old_bad
                if diff != 0:
                    dv += diff
                    dw += diff * clause_weights[c_idx]

            if dv < 0:
                align = x_cont[v] if cur == 0 else (1.0 - x_cont[v])
                if (
                    dv < best_dv
                    or (dv == best_dv and dw < best_dw - 1e-12)
                    or (dv == best_dv and abs(dw - best_dw) <= 1e-12 and align > best_align)
                ):
                    best_dv = dv
                    best_dw = dw
                    best_align = align
                    best_var = v
            elif dv == 0 and best_dv >= 0 and plateau_used < max_plateau and v not in plateau_flipped:
                if dw < -1e-9:
                    align = x_cont[v] if cur == 0 else (1.0 - x_cont[v])
                    if (
                        best_dv > 0
                        or dw < best_dw - 1e-12
                        or (abs(dw - best_dw) <= 1e-12 and align > best_align)
                    ):
                        best_dv = 0
                        best_dw = dw
                        best_align = align
                        best_var = v

        if best_var < 0:
            break

        if best_dv == 0:
            plateau_used += 1
            plateau_flipped.add(best_var)
        else:
            plateau_flipped.clear()

        # Apply flip
        cur = assign[best_var]
        delta_x = 1 if cur == 0 else -1
        assign[best_var] = 1 - cur
        for c_idx, coeff in var_clauses[best_var]:
            clause_sum[c_idx] += delta_x * coeff
        viol_count += best_dv

    viol_clauses = [j for j in range(m) if clause_sum[j] != 1]
    return assign, viol_count, viol_clauses


def _compute_hamiltonian_grad(
    phi: Sequence[float],
    lam: Sequence[float],
    w_clause: Sequence[float],
    inc: SparseIncidence,
    rho: float,
    alpha_k: float,
    gamma_wf: float,
    gamma_beat: float,
    beta_t: float,
) -> tuple[list[float], list[float], list[float], float, float, float]:
    """Evaluate x(phi), residuals r, and exact Hamiltonian gradient grad_phi H.

    Returns (x, r, grad_phi, res_inf, res_l2, igap).
    """
    n = inc.n_vars
    m = inc.m_clauses
    clauses = inc.clauses
    degrees = inc.degrees

    cos_phi = [math.cos(ph) for ph in phi]
    sin_phi = [math.sin(ph) for ph in phi]
    x = [0.5 * (1.0 - sg) for sg in cos_phi]

    r = [0.0] * m
    gx_lin = [0.0] * n
    ata_x = [0.0] * n
    dU_dsigma = [0.0] * n

    res_inf = 0.0
    r2_sq = 0.0
    inv_w1 = 1.0 / _OMEGA_1
    inv_w2 = 1.0 / _OMEGA_2

    for j, (a, b, c) in enumerate(clauses):
        ax_j = x[a] + x[b] + x[c]
        rj = ax_j - 1.0
        r[j] = rj

        ar = -rj if rj < 0.0 else rj
        if ar > res_inf:
            res_inf = ar
        r2_sq += rj * rj

        wj = w_clause[j]
        beat_j = math.sin(_OMEGA_1 * rj) * inv_w1 + math.sin(_OMEGA_2 * rj) * inv_w2
        drive_j = (wj + rho) * rj + lam[j] + gamma_beat * beat_j

        gx_lin[a] += drive_j
        gx_lin[b] += drive_j
        gx_lin[c] += drive_j

        # Accumulate A^T (A x) for K x = A^T (A x) - d * x
        ata_x[a] += ax_j
        ata_x[b] += ax_j
        ata_x[c] += ax_j

        # Exact Walsh-Hadamard 1-in-3 clause gradient w.r.t. sigma = cos(phi)
        sa = cos_phi[a]
        sb = cos_phi[b]
        sc = cos_phi[c]
        wj_8 = 0.125 * wj
        dU_dsigma[a] += wj_8 * (-1.0 + sb + sc + 3.0 * sb * sc)
        dU_dsigma[b] += wj_8 * (-1.0 + sa + sc + 3.0 * sa * sc)
        dU_dsigma[c] += wj_8 * (-1.0 + sa + sb + 3.0 * sa * sb)

    grad_phi = [0.0] * n
    igap = 0.0
    for i in range(n):
        xi = x[i]
        gi_gap = xi if xi <= 0.5 else (1.0 - xi)
        if gi_gap > igap:
            igap = gi_gap

        s_i = sin_phi[i]
        kx_i = ata_x[i] - degrees[i] * xi if degrees[i] > 0 else ata_x[i]
        g_xi = gx_lin[i] + alpha_k * kx_i
        # Pullback + Walsh-Hadamard + Boolean pinning
        grad_phi[i] = (
            0.5 * s_i * g_xi
            - gamma_wf * s_i * dU_dsigma[i]
            + beta_t * s_i * cos_phi[i]
        )

    res_l2 = math.sqrt(r2_sq / m) if m > 0 else 0.0
    return x, r, grad_phi, res_inf, res_l2, igap


def _record_vector_telemetry(ledger: BitLedger, vec: Sequence[float]) -> None:
    """Record min/max nonzero magnitudes and any non-finite values of vec into BitLedger."""
    max_val = 0.0
    min_val = math.inf
    for v in vec:
        if not math.isfinite(v):
            ledger.record_float(v, count_op=True)
            return
        av = -v if v < 0.0 else v
        if av > 0.0:
            if av > max_val:
                max_val = av
            if av < min_val:
                min_val = av
    if max_val > 0.0:
        ledger.record_float(max_val, count_op=True)
    if min_val < math.inf and min_val != max_val:
        ledger.record_float(min_val, count_op=True)


def solve_track_b(
    instance: Monotone1in3Instance,
    config: SolverConfig | None = None,
) -> SolverResult:
    """Solve Monotone 1-in-3 SAT via Symplectic Leapfrog + Polyrhythmic Phase-Kick Annealing."""
    t_start = time.perf_counter()
    cfg = config or SolverConfig()
    n = instance.n_vars
    m = instance.m_clauses

    ledger = BitLedger(
        max_int_bits_limit=cfg.max_int_bits_limit,
        max_fraction_bits_limit=cfg.max_fraction_bits_limit,
        raise_on_guardrail=True,
    )

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

    # Deterministic polynomial step budget T_max(n, m)
    max_iters = cfg.max_iters if cfg.max_iters is not None else min(2400, 24 * n + 400)
    b_s_eff = max(cfg.B_s, 1.0)

    try:
        inc = build_incidence(instance)
        ata_int = inc.compute_ata_matrix()

        # Instrument exact integer degrees and A^T A entries in BitLedger
        for d in inc.degrees:
            ledger.record_int(d, count_op=False)
        for i in range(n):
            row = ata_int[i]
            for j in range(n):
                val = row[j]
                if val != 0:
                    ledger.record_int(val, count_op=True)
            if inc.degrees[i] > 0:
                ledger.record_int(row[i] - inc.degrees[i], count_op=True)

        b_s_eff = max(cfg.B_s, float(inc.max_degree) + 2.0 * cfg.eps_chol + 1.0)
        kappa2_bound = (18.0 * m + b_s_eff) / cfg.eps_chol

        # Precompute M_0 = I + eta_0 A^T A via square-root-free LDL^T from primitives.py
        m0_tracked = _build_m0_tracked(ata_int, cfg.eta_0, ledger)
        m0_fac = ldlt_factor(m0_tracked, ledger, mode="float64")
        if m0_fac is None:
            raise RuntimeError("Unexpected non-SPD M_0")
        m0_offdiag, m0_d_inv = _extract_ldlt_raw(m0_fac)

        # Initialize torus phases phi^(0) breaking 1/3 symmetry using Walsh + golden-angle spread
        phi_base = math.acos(1.0 / 3.0)
        phi = [
            (
                phi_base
                + 0.45 * math.sin(_TWO_PI * (i + 1) / (n + 1) + _OMEGA_GOLD * i)
                + 0.20 * _walsh_sign(i + 1, 3)
            )
            % _TWO_PI
            for i in range(n)
        ]
        p = [0.0] * n
        lam = [0.0] * m
        w_clause = [1.0] * m

        # Symplectic & annealing hyperparameters
        tau = min(0.28, max(0.08, cfg.tau_step * 1.8))
        half_tau = 0.5 * tau
        rho = cfg.rho
        alpha_k = cfg.alpha_k
        gamma_wf = cfg.gamma_wf
        gamma_beat = cfg.gamma_beat
        eta_d = cfg.eta_d
        damp_d = 1.0 - eta_d * cfg.delta_d
        b_lambda = cfg.B_lambda
        gamma_min = 0.78
        gamma_max = 0.96
        beta_min = cfg.beta_min
        beta_max = cfg.beta_max
        cycle_len = max(50, min(140, 2 * n + 20))
        w_stall = max(10, min(20, cfg.w_stall))
        polish_steps = max(20, 2 * n)

        # Dual spectral certificate state (LDL^T-certified)
        y_cert = [0.0] * m
        y_cert_prev = [0.0] * m
        s_cert = [min(b_s_eff, float(inc.degrees[i]) + 2.0 * cfg.eps_chol) for i in range(n)]
        m_cert_sh = _build_m_cert_tracked(ata_int, inc.degrees, s_cert, ledger, shift_diag=cfg.eps_chol)
        cert_pd_verified = ldlt_factor(m_cert_sh, ledger, mode="float64") is not None
        m_cert_full = _build_m_cert_tracked(ata_int, inc.degrees, s_cert, ledger, shift_diag=0.0)
        l_cert_fac = ldlt_factor(m_cert_full, ledger, mode="float64")
        if l_cert_fac is not None:
            cert_offdiag, cert_d_inv = _extract_ldlt_raw(l_cert_fac)
        else:
            cert_offdiag, cert_d_inv = (), ()

        dual_interval = 1 if n <= 30 else 2
        b_cert = cfg.dual_update_interval if cfg.dual_update_interval is not None else max(8, n // 2)
        dual_steps_done = 0

        # Tracking state
        best_d_spec = -math.inf
        best_candidate: tuple[int, ...] | None = None
        best_violations = m + 1
        best_viol_clauses: list[int] = list(range(m))
        best_r2_seen = math.inf
        stall_counter = 0
        kick_epoch = 0

        last_res_inf = 1.0
        last_res_l2 = 1.0
        last_igap = 0.5
        last_dual_res = 0.0
        last_x = [1.0 / 3.0] * n
        iter_history: list[dict[str, Any]] = []

        # Initial gradient evaluation at t=0
        x, r, grad_phi, res_inf, res_l2, igap = _compute_hamiltonian_grad(
            phi, lam, w_clause, inc, rho, alpha_k, gamma_wf, gamma_beat, beta_min
        )
        x_prev = x

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
                    final_x=tuple(last_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            ledger.begin_iteration(t)
            last_x = x
            last_res_inf = res_inf
            last_res_l2 = res_l2
            last_igap = igap

            # Check non-finite overflow early
            if not (math.isfinite(res_inf) and math.isfinite(res_l2)):
                ledger.record_float(res_inf, count_op=True)
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
                    final_x=tuple(x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            # 1. Discrete rounding + deterministic 1-flip polish (every step for small n, every 2 steps for n=60)
            do_round = (t == 0) or (n <= 30) or ((t & 1) == 0) or (t == max_iters - 1)
            cur_viol_clauses: list[int] = []
            if do_round:
                cand_thr = [1 if xi >= 0.5 else 0 for xi in x]
                cand_grd = _greedy_conflict_round_fast(x, inc)

                for cand_raw in (cand_thr, cand_grd):
                    polished, vcount, vclauses = _deterministic_1flip_polish(
                        cand_raw, x, w_clause, inc, max_steps=polish_steps
                    )
                    if vcount == 0:
                        ver = verify_assignment(instance, polished)
                        if ver.is_sat:
                            _record_vector_telemetry(ledger, x)
                            _record_vector_telemetry(ledger, p)
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
                                assignment=tuple(polished),
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
                                verification=ver,
                                best_candidate=tuple(polished),
                                termination_reason="SAT_FOUND",
                                final_x=tuple(x),
                                max_kappa2_cert_bound=kappa2_bound,
                            )
                    if vcount < best_violations:
                        best_violations = vcount
                        best_candidate = tuple(polished)
                        best_viol_clauses = vclauses
                        stall_counter = 0
                    if not cur_viol_clauses or len(vclauses) < len(cur_viol_clauses):
                        cur_viol_clauses = vclauses

            # 2. Cosine-annealed damping gamma(t) & Boolean pinning beta(t)
            u_cyc = float(t % cycle_len) / float(cycle_len)
            cos_factor = 0.5 * (1.0 + math.cos(math.pi * u_cyc))
            gamma_t = gamma_min + (gamma_max - gamma_min) * cos_factor
            beta_t = beta_min + (beta_max - beta_min) * (1.0 - cos_factor)

            # 3. Störmer-Verlet (leapfrog) symplectic step
            # (a) Half-kick momentum
            p_half = [0.0] * n
            for i in range(n):
                pi = gamma_t * p[i] - half_tau * grad_phi[i]
                if pi > _MOMENTUM_CLAMP:
                    pi = _MOMENTUM_CLAMP
                elif pi < -_MOMENTUM_CLAMP:
                    pi = -_MOMENTUM_CLAMP
                elif -_MOMENTUM_FLUSH < pi < _MOMENTUM_FLUSH:
                    pi = 0.0
                p_half[i] = pi

            # (b) Full drift position using precomputed LDL^T of M_0
            vel = _ldlt_solve_raw(m0_offdiag, m0_d_inv, p_half)
            phi_next = [(phi[i] + tau * vel[i]) % _TWO_PI for i in range(n)]

            # (c) Re-evaluate Hamiltonian gradient at drifted phi_next
            x_next, r_next, grad_next, res_inf_next, res_l2_next, igap_next = _compute_hamiltonian_grad(
                phi_next, lam, w_clause, inc, rho, alpha_k, gamma_wf, gamma_beat, beta_t
            )

            # (d) Second half-kick momentum
            p_next = [0.0] * n
            dual_res = 0.0
            for i in range(n):
                pi = gamma_t * p_half[i] - half_tau * grad_next[i]
                if pi > _MOMENTUM_CLAMP:
                    pi = _MOMENTUM_CLAMP
                elif pi < -_MOMENTUM_CLAMP:
                    pi = -_MOMENTUM_CLAMP
                elif -_MOMENTUM_FLUSH < pi < _MOMENTUM_FLUSH:
                    pi = 0.0
                p_next[i] = pi
                dp = abs(pi - p[i])
                if dp > dual_res:
                    dual_res = dp

            # 4. Over-relaxed primal-dual Lagrange multiplier update + dynamic clause reweighting
            theta = cfg.theta_pdhg
            x_bar = [x_next[i] + theta * (x_next[i] - x_prev[i]) for i in range(n)]
            for j, (a, b, c) in enumerate(inc.clauses):
                r_bar = x_bar[a] + x_bar[b] + x_bar[c] - 1.0
                new_lam = damp_d * lam[j] + eta_d * r_bar
                if new_lam > b_lambda:
                    new_lam = b_lambda
                elif new_lam < -b_lambda:
                    new_lam = -b_lambda
                dl = abs(new_lam - lam[j])
                if dl > dual_res:
                    dual_res = dl
                lam[j] = new_lam

                # Smooth dynamic clause weight adaptation on frustrated residuals
                rj = r_next[j]
                if rj * rj > 0.04:
                    wj = w_clause[j] + 0.08 * (rj * rj)
                    w_clause[j] = wj if wj <= _WEIGHT_MAX else _WEIGHT_MAX
                else:
                    wj = 0.995 * w_clause[j] + 0.005 * _WEIGHT_MIN
                    w_clause[j] = wj if wj >= _WEIGHT_MIN else _WEIGHT_MIN

            last_dual_res = dual_res

            # 5. Stagnation detection & Polyrhythmic Walsh-Hadamard Phase-Kick Schedule
            if res_l2_next < best_r2_seen - cfg.eps_imp:
                best_r2_seen = res_l2_next
                stall_counter = 0
            else:
                stall_counter += 1

            at_cycle_end = (t + 1) % cycle_len == 0
            if stall_counter >= w_stall or at_cycle_end:
                stall_counter = 0
                kick_epoch += 1
                best_r2_seen = res_l2_next

                # Identify frustrated clauses (either discrete violated or high continuous residual)
                frustrated = cur_viol_clauses if cur_viol_clauses else best_viol_clauses
                if not frustrated:
                    frustrated = [j for j in range(m) if abs(r_next[j]) > 0.12]

                # Boost frustrated clause weights & normalize if needed
                max_w = _WEIGHT_MIN
                for j in frustrated:
                    wj = w_clause[j] + (1.2 if at_cycle_end else 0.5)
                    if wj > _WEIGHT_MAX:
                        wj = _WEIGHT_MAX
                    w_clause[j] = wj
                    if wj > max_w:
                        max_w = wj
                if max_w > 0.85 * _WEIGHT_MAX:
                    scale_w = 0.65
                    for j in range(m):
                        w_clause[j] = max(_WEIGHT_MIN, w_clause[j] * scale_w)

                # Apply Walsh-Hadamard polyrhythmic phase & momentum kicks on frustrated clauses
                kick_amp = 1.15 if at_cycle_end else 0.70
                dphi = [0.0] * n
                dp_kick = [0.0] * n

                # Alternating symplectic wave-injection from best near-SAT candidate
                # (only when within 2 violations, every 3rd kick epoch so global flow stays strong)
                inject_from_best = (
                    best_candidate is not None
                    and best_violations <= 2
                    and (kick_epoch % 3) == 0
                )
                if inject_from_best and best_candidate is not None:
                    for i in range(n):
                        base_ang = (math.pi - 0.18) if best_candidate[i] == 1 else 0.18
                        phi_next[i] = base_ang
                        p_next[i] *= 0.25

                # Build 1-hop neighborhood of frustrated clauses for coupled gadget tunneling
                frustrated_vars: set[int] = set()
                for j in frustrated:
                    a, b, c = inc.clauses[j]
                    frustrated_vars.add(a)
                    frustrated_vars.add(b)
                    frustrated_vars.add(c)

                neighbor_vars: set[int] = set()
                for v in frustrated_vars:
                    for c_idx, _ in inc.var_clauses[v]:
                        ca, cb, cc = inc.clauses[c_idx]
                        neighbor_vars.add(ca)
                        neighbor_vars.add(cb)
                        neighbor_vars.add(cc)
                neighbor_vars.difference_update(frustrated_vars)

                for j in frustrated:
                    a, b, c = inc.clauses[j]
                    vars_c = (a, b, c)
                    rj = r_next[j]
                    # Pick one Walsh-modulated literal slot to invert strongly, others counter-kick
                    slot_sel = (kick_epoch + j + (kick_epoch ^ j).bit_count()) % 3
                    for s_idx, v in enumerate(vars_c):
                        w_sgn = _walsh_sign(kick_epoch + j + 1, v + s_idx + 1)
                        beat = (
                            math.cos(_OMEGA_1 * kick_epoch + _OMEGA_2 * j + _OMEGA_3 * s_idx)
                            - 0.6 * math.cos(_OMEGA_GOLD * (kick_epoch + v))
                        )
                        if s_idx == slot_sel:
                            if inject_from_best and best_candidate is not None:
                                # Strongly drive selected literal across the 0 <-> pi barrier
                                target_dir = (math.pi - phi_next[v]) if best_candidate[v] == 0 else (-phi_next[v])
                                dphi[v] += 0.95 * target_dir + 0.25 * beat
                                dp_kick[v] += 1.2 * (1.0 if target_dir >= 0.0 else -1.0)
                            elif rj < -0.1:
                                target_dir = math.pi - phi_next[v]
                                dphi[v] += kick_amp * (0.75 * target_dir + 0.35 * beat)
                                dp_kick[v] += 0.7 * kick_amp * (w_sgn + 0.5 * beat)
                            elif rj > 0.1:
                                target_dir = -phi_next[v]
                                dphi[v] += kick_amp * (0.75 * target_dir + 0.35 * beat)
                                dp_kick[v] += 0.7 * kick_amp * (w_sgn + 0.5 * beat)
                            else:
                                target_dir = w_sgn * 1.4
                                dphi[v] += kick_amp * (0.75 * target_dir + 0.35 * beat)
                                dp_kick[v] += 0.7 * kick_amp * (w_sgn + 0.5 * beat)
                        else:
                            dphi[v] += 0.40 * kick_amp * w_sgn * beat
                            dp_kick[v] += 0.35 * kick_amp * w_sgn * beat

                # Propagate phase-shifted Walsh harmonic ripple to 1-hop coupled variables
                for v in neighbor_vars:
                    w_sgn = _walsh_sign(kick_epoch + 3, v + 1)
                    ripple = w_sgn * math.sin(_OMEGA_1 * kick_epoch + _OMEGA_GOLD * v)
                    dphi[v] += 0.45 * kick_amp * ripple
                    dp_kick[v] += 0.55 * kick_amp * ripple

                # Mild global polyrhythmic de-phasing to escape global 0.333 / 0.5 saddle
                glob_amp = 0.08 if inject_from_best else (0.28 if at_cycle_end else 0.12)
                for i in range(n):
                    g_harm = _walsh_sign(kick_epoch, i + 1) * math.sin(
                        _OMEGA_1 * i + _OMEGA_2 * kick_epoch + _OMEGA_GOLD * (i % 7)
                    )
                    phi_next[i] = (phi_next[i] + dphi[i] + glob_amp * g_harm) % _TWO_PI
                    pi_new = p_next[i] + dp_kick[i] + 0.5 * glob_amp * g_harm
                    if pi_new > _MOMENTUM_CLAMP:
                        pi_new = _MOMENTUM_CLAMP
                    elif pi_new < -_MOMENTUM_CLAMP:
                        pi_new = -_MOMENTUM_CLAMP
                    p_next[i] = pi_new

                # Refresh gradient after kick for next Störmer-Verlet step
                x_next, r_next, grad_next, res_inf_next, res_l2_next, igap_next = _compute_hamiltonian_grad(
                    phi_next, lam, w_clause, inc, rho, alpha_k, gamma_wf, gamma_beat, beta_t
                )

            phi = phi_next
            p = p_next
            x_prev = x
            x = x_next
            r = r_next
            grad_phi = grad_next
            res_inf = res_inf_next
            res_l2 = res_l2_next
            igap = igap_next

            # 6. Sound LDL^T-certified spectral dual UNSAT ascent (D_spec)
            d_spec_float = best_d_spec
            if l_cert_fac is not None and (t % dual_interval == 0):
                dual_steps_done += 1
                d_spec_raw, x_dual, grad_y, grad_s = _eval_dual_raw(
                    y_cert, s_cert, cert_offdiag, cert_d_inv, inc
                )
                d_spec_float = d_spec_raw
                if math.isfinite(d_spec_raw) and d_spec_raw > best_d_spec:
                    best_d_spec = d_spec_raw

                x_norm_sq = sum(xd * xd for xd in x_dual)
                eps_cert = 1e-6 + (n * n) * _EPS_MACH * kappa2_bound * x_norm_sq

                if cert_pd_verified and math.isfinite(d_spec_raw) and d_spec_raw > eps_cert:
                    # Independent LDL^T verification via primitives.ldlt_factor / ldlt_solve
                    verified_unsat, verified_d_spec = _verify_dual_certificate_ldlt(
                        y_cert, s_cert, ata_int, inc, cfg.eps_chol, kappa2_bound, ledger
                    )
                    if verified_unsat:
                        _record_vector_telemetry(ledger, x)
                        _record_vector_telemetry(ledger, p)
                        bit_snap = ledger.end_iteration()
                        if cfg.record_iter_history:
                            iter_history.append({
                                "iteration": t,
                                "primal_res_inf": res_inf,
                                "primal_res_l2": res_l2,
                                "integrality_gap": igap,
                                "d_spec": verified_d_spec,
                                **bit_snap,
                            })
                        return SolverResult(
                            status="UNSAT_CERTIFIED",
                            assignment=None,
                            dual_certificate_value=verified_d_spec,
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
                            termination_reason="UNSAT_CERT",
                            final_x=tuple(x),
                            max_kappa2_cert_bound=kappa2_bound,
                        )

                # Mild Nesterov-accelerated projected ascent on y_cert
                mom_y = 0.35 if dual_steps_done > 2 else 0.0
                alpha_y = cfg.alpha_y
                b_y = cfg.B_y
                y_new = [0.0] * m
                for j in range(m):
                    y_ext = y_cert[j] + mom_y * (y_cert[j] - y_cert_prev[j])
                    yj = y_ext + alpha_y * grad_y[j]
                    if yj > b_y:
                        yj = b_y
                    elif yj < -b_y:
                        yj = -b_y
                    y_new[j] = yj
                y_cert_prev = y_cert
                y_cert = y_new

                # Periodically update s_cert with fast LDL^T screen + primitives.ldlt_factor verification
                if dual_steps_done % b_cert == 0:
                    step_s = cfg.alpha_s
                    s_accepted = False
                    for _ in range(cfg.k_bt):
                        s_cand = [0.0] * n
                        for i in range(n):
                            sc = s_cert[i] + step_s * grad_s[i]
                            if sc > b_s_eff:
                                sc = b_s_eff
                            elif sc < -b_s_eff:
                                sc = -b_s_eff
                            if inc.degrees[i] == 0 and sc < 2.0 * cfg.eps_chol:
                                sc = 2.0 * cfg.eps_chol
                            s_cand[i] = sc
                        ok_sh, _, _ = _ldlt_is_spd_raw(ata_int, inc.degrees, s_cand, cfg.eps_chol)
                        if ok_sh:
                            ok_full, off_new, dinv_new = _ldlt_is_spd_raw(ata_int, inc.degrees, s_cand, 0.0)
                            if ok_full:
                                s_cert = s_cand
                                cert_offdiag, cert_d_inv = off_new, dinv_new
                                cert_pd_verified = True
                                s_accepted = True
                                break
                        step_s *= 0.5

                    if not s_accepted:
                        ok_cur, sh_off, sh_dinv = _ldlt_is_spd_raw(ata_int, inc.degrees, s_cert, cfg.eps_chol)
                        if ok_cur:
                            margins = _ldlt_diag_margins_raw(sh_off, sh_dinv)
                            for budget in (0.85, 0.50):
                                s_cand = list(s_cert)
                                dec_entries: list[tuple[float, int, float]] = []
                                for i in range(n):
                                    if grad_s[i] >= 0.0:
                                        sc = s_cert[i] + cfg.alpha_s * grad_s[i]
                                        s_cand[i] = sc if sc <= b_s_eff else b_s_eff
                                    else:
                                        dec_i = -(cfg.alpha_s * grad_s[i])
                                        if inc.degrees[i] == 0:
                                            max_d0 = s_cert[i] - 2.0 * cfg.eps_chol
                                            if max_d0 <= 0.0:
                                                dec_i = 0.0
                                            elif dec_i > max_d0:
                                                dec_i = max_d0
                                        max_box = s_cert[i] + b_s_eff
                                        if dec_i > max_box:
                                            dec_i = max_box
                                        if dec_i > 0.0 and margins[i] > 0.0:
                                            dec_entries.append((dec_i / margins[i], i, dec_i))
                                dec_entries.sort(key=lambda item: item[0])
                                cum_ratio = 0.0
                                for r_i, i, dec_i in dec_entries:
                                    if cum_ratio + r_i <= budget:
                                        s_cand[i] = s_cert[i] - dec_i
                                        cum_ratio += r_i
                                    else:
                                        rem = budget - cum_ratio
                                        if rem > 0.0:
                                            s_cand[i] = s_cert[i] - rem * margins[i]
                                        break
                                ok_sh, _, _ = _ldlt_is_spd_raw(ata_int, inc.degrees, s_cand, cfg.eps_chol)
                                if ok_sh:
                                    ok_full, off_new, dinv_new = _ldlt_is_spd_raw(
                                        ata_int, inc.degrees, s_cand, 0.0
                                    )
                                    if ok_full:
                                        s_cert = s_cand
                                        cert_offdiag, cert_d_inv = off_new, dinv_new
                                        cert_pd_verified = True
                                        break

            # Instrument float telemetry in BitLedger
            if (t & 3) == 0 or t == max_iters - 1:
                _record_vector_telemetry(ledger, x)
                _record_vector_telemetry(ledger, p)
                _record_vector_telemetry(ledger, lam)
                _record_vector_telemetry(ledger, w_clause)

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
                    final_x=tuple(last_x),
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
            final_x=tuple(last_x),
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
            max_kappa2_cert_bound=(18.0 * m + b_s_eff) / cfg.eps_chol,
        )
