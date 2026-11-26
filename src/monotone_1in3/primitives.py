"""Mathematical operators for the four structural primitives of PD-PFGC.

Strictly isolated from generators.py, harness.py, and any external SAT/CSP/ILP solvers.
All numerical operations route through BitLedger-instrumented tracked scalars.
"""

from __future__ import annotations

from dataclasses import dataclass
import math
from typing import Sequence

from .bitwidth import (
    BitLedger,
    TrackedDecimal,
    TrackedFloat,
    TrackedFraction,
    TrackedInt,
    TrackedScalar,
    make_scalar,
    t_cos,
    t_sin,
    t_sqrt,
)
from .instance import SparseIncidence


def is_finite_scalar(val: TrackedScalar) -> bool:
    """Return True iff tracked scalar value is finite in its native precision."""
    t = type(val)
    if t is TrackedFloat:
        return math.isfinite(val.value)
    if t is TrackedDecimal:
        return val.value.is_finite()
    if t is TrackedFraction:
        return True
    return math.isfinite(float(val))


def is_zero_scalar(val: TrackedScalar) -> bool:
    """Return True iff tracked scalar value is exact zero in its native precision."""
    t = type(val)
    if t is TrackedFloat:
        return val.value == 0.0
    if t is TrackedDecimal:
        return val.value == 0
    if t is TrackedFraction:
        return val.value == 0
    return val == 0


def is_pos_scalar(val: TrackedScalar) -> bool:
    """Return True iff tracked scalar value is strictly positive in its native precision."""
    t = type(val)
    if t is TrackedFloat:
        return val.value > 0.0
    if t is TrackedDecimal:
        return val.value > 0
    if t is TrackedFraction:
        return val.value > 0
    return val > 0


@dataclass(frozen=True)
class CholeskyFactor:
    """Lower-triangular Cholesky factor L such that L L^T = M."""

    size: int
    L: list[list[TrackedScalar]]
    # Sparse off-diagonal (col_idx, L[row][col]) pairs for fast exact triangular solves
    offdiag_nz: tuple[tuple[tuple[int, TrackedScalar], ...], ...]
    diag: tuple[TrackedScalar, ...]


class SparseOperators:
    """Precomputed sparse graph/hypergraph operators A, A^T, d, K, D_K^{-1/2}, and F_spec."""

    def __init__(
        self,
        incidence: SparseIncidence,
        ledger: BitLedger,
        mode: str = "float64",
        decimal_prec: int = 80,
    ) -> None:
        self.inc = incidence
        self.n = incidence.n_vars
        self.m = incidence.m_clauses
        self.ledger = ledger
        self.mode = mode
        self.decimal_prec = decimal_prec

        self.zero = make_scalar(0, ledger, mode=mode, decimal_prec=decimal_prec)
        self.one = make_scalar(1, ledger, mode=mode, decimal_prec=decimal_prec)
        self.two = make_scalar(2, ledger, mode=mode, decimal_prec=decimal_prec)
        self.half = make_scalar(0.5, ledger, mode=mode, decimal_prec=decimal_prec)
        self.eighth = make_scalar(0.125, ledger, mode=mode, decimal_prec=decimal_prec)
        self.three = make_scalar(3, ledger, mode=mode, decimal_prec=decimal_prec)

        # Record exact integer degree and conflict-matrix entries in BitLedger
        self.degrees_int = [TrackedInt(d, ledger, count_op=False) for d in incidence.degrees]
        self.degrees_s = [make_scalar(d, ledger, mode=mode, decimal_prec=decimal_prec) for d in incidence.degrees]

        # Precompute and cache exact integer A^T A in BitLedger via TrackedInt
        zero_ti = TrackedInt(0, ledger, count_op=False)
        ata_ti: list[list[TrackedInt]] = [[zero_ti] * self.n for _ in range(self.n)]
        for terms in incidence.clause_terms:
            for i, ci in terms:
                row_i = ata_ti[i]
                ci_t = TrackedInt(ci, ledger, count_op=False)
                for k, ck in terms:
                    ck_t = TrackedInt(ck, ledger, count_op=False)
                    row_i[k] = row_i[k] + (ci_t * ck_t)
        self.ata_int = ata_ti
        for i in range(self.n):
            if incidence.degrees[i] > 0:
                _ = ata_ti[i][i] - self.degrees_int[i]
        self.ata_s: list[list[TrackedScalar]] = [
            [
                make_scalar(cell.value, ledger, mode=mode, decimal_prec=decimal_prec)
                for cell in row
            ]
            for row in ata_ti
        ]

        # D_K diagonal: (D_K)_ii = max(1, sum_k K_ik) = max(1, 2 * d_i)
        self.inv_sqrt_dk: list[TrackedScalar] = []
        for d in incidence.degrees:
            dk_ii = 2 * d if d > 0 else 1
            dk_s = make_scalar(dk_ii, ledger, mode=mode, decimal_prec=decimal_prec)
            self.inv_sqrt_dk.append(self.one / t_sqrt(dk_s))

    def apply_A(self, x: Sequence[TrackedScalar]) -> list[TrackedScalar]:
        """Compute y = A x in O(m) via sparse clause incidence."""
        res: list[TrackedScalar] = []
        for terms in self.inc.clause_terms:
            acc = self.zero
            for v_idx, coeff in terms:
                if coeff == 1:
                    acc = acc + x[v_idx]
                elif coeff == 2:
                    acc = acc + (self.two * x[v_idx])
                else:
                    acc = acc + (self.three * x[v_idx])
            res.append(acc)
        return res

    def apply_AT(self, y: Sequence[TrackedScalar]) -> list[TrackedScalar]:
        """Compute z = A^T y in O(m) via sparse variable-clause incidence."""
        res: list[TrackedScalar] = []
        for v_clauses in self.inc.var_clauses:
            acc = self.zero
            for c_idx, coeff in v_clauses:
                if coeff == 1:
                    acc = acc + y[c_idx]
                elif coeff == 2:
                    acc = acc + (self.two * y[c_idx])
                else:
                    acc = acc + (self.three * y[c_idx])
            res.append(acc)
        return res

    def apply_K(self, x: Sequence[TrackedScalar]) -> list[TrackedScalar]:
        """Compute K x = A^T (A x) - d * x in O(m + n)."""
        ax = self.apply_A(x)
        ata_x = self.apply_AT(ax)
        out: list[TrackedScalar] = []
        for i in range(self.n):
            if self.inc.degrees[i] == 0:
                out.append(ata_x[i])
            else:
                out.append(ata_x[i] - self.degrees_s[i] * x[i])
        return out

    def apply_F_spec(self, v: Sequence[TrackedScalar], eta_spec: TrackedScalar) -> list[TrackedScalar]:
        """Compute F_spec v = (I - eta_spec D_K^{-1/2} K D_K^{-1/2}) v in O(m + n)."""
        scaled = [self.inv_sqrt_dk[i] * v[i] for i in range(self.n)]
        k_scaled = self.apply_K(scaled)
        out: list[TrackedScalar] = []
        for i in range(self.n):
            out.append(v[i] - eta_spec * (self.inv_sqrt_dk[i] * k_scaled[i]))
        return out


def build_M0(ops: SparseOperators, eta_0: TrackedScalar) -> list[list[TrackedScalar]]:
    """Construct dense SPD global normal preconditioner M_0 = I_n + eta_0 A^T A."""
    n = ops.n
    ata_s = ops.ata_s
    mat: list[list[TrackedScalar]] = []
    for i in range(n):
        row: list[TrackedScalar] = []
        ata_row = ata_s[i]
        for j in range(n):
            val = eta_0 * ata_row[j]
            if i == j:
                val = ops.one + val
            row.append(val)
        mat.append(row)
    return mat


def build_M_cert(
    ops: SparseOperators,
    s_cert: Sequence[TrackedScalar],
    shift_diag: TrackedScalar | None = None,
) -> list[list[TrackedScalar]]:
    """Construct M_cert(s) = K + A^T A + diag(s) (- shift_diag * I if given)."""
    n = ops.n
    ata_s = ops.ata_s
    # K + A^T A = 2 A^T A - diag(d)
    mat: list[list[TrackedScalar]] = []
    for i in range(n):
        row: list[TrackedScalar] = []
        ata_row = ata_s[i]
        for j in range(n):
            val = ops.two * ata_row[j]
            if i == j:
                val = val - ops.degrees_s[i] + s_cert[i]
                if shift_diag is not None:
                    val = val - shift_diag
            row.append(val)
        mat.append(row)
    return mat


def cholesky_factor(
    mat: Sequence[Sequence[TrackedScalar]],
    ledger: BitLedger,
    mode: str = "float64",
    decimal_prec: int = 80,
) -> CholeskyFactor | None:
    """Compute Cholesky factorization L L^T = mat. Returns None if not strictly SPD."""
    n = len(mat)
    zero = make_scalar(0, ledger, mode=mode, decimal_prec=decimal_prec)
    L: list[list[TrackedScalar]] = [[zero] * n for _ in range(n)]
    offdiag_nz: list[tuple[tuple[int, TrackedScalar], ...]] = []
    diag: list[TrackedScalar] = []

    for i in range(n):
        row_L = L[i]
        row_mat = mat[i]
        nz_list: list[tuple[int, TrackedScalar]] = []
        for j in range(i):
            s = row_mat[j]
            for k, ljk in offdiag_nz[j]:
                lik = row_L[k]
                if not is_zero_scalar(lik):
                    s = s - lik * ljk
            val = s / diag[j]
            if not is_finite_scalar(val):
                return None
            row_L[j] = val
            if not is_zero_scalar(val):
                nz_list.append((j, val))

        diag_s = row_mat[i]
        for _, lik in nz_list:
            diag_s = diag_s - lik * lik
        if not is_finite_scalar(diag_s) or not is_pos_scalar(diag_s):
            return None
        d_val = t_sqrt(diag_s)
        if not is_finite_scalar(d_val) or not is_pos_scalar(d_val):
            return None
        row_L[i] = d_val
        diag.append(d_val)
        offdiag_nz.append(tuple(nz_list))

    return CholeskyFactor(
        size=n,
        L=L,
        offdiag_nz=tuple(offdiag_nz),
        diag=tuple(diag),
    )


def cholesky_solve(factor: CholeskyFactor, rhs: Sequence[TrackedScalar]) -> list[TrackedScalar]:
    """Solve (L L^T) x = rhs using sparse nonzero representation of L."""
    n = factor.size
    y: list[TrackedScalar] = [rhs[0]] * n
    for i in range(n):
        s = rhs[i]
        for j, l_ij in factor.offdiag_nz[i]:
            s = s - l_ij * y[j]
        y[i] = s / factor.diag[i]

    # Transpose back-substitution: build column view implicitly by subtracting from rhs buffer
    x = list(y)
    for j in range(n - 1, -1, -1):
        xj = x[j] / factor.diag[j]
        x[j] = xj
        if not is_zero_scalar(xj):
            # Subtract L^T contributions from indices < j using row j of L
            for k, l_jk in factor.offdiag_nz[j]:
                x[k] = x[k] - l_jk * xj
    return x


def cholesky_diag_margins(
    factor: CholeskyFactor,
    ledger: BitLedger,
    mode: str = "float64",
    decimal_prec: int = 80,
) -> list[TrackedScalar]:
    """Compute exact single-coordinate PD margins mu_i = 1 / ((L L^T)^{-1})_{ii} in (1/6) n^3 ops."""
    n = factor.size
    zero = make_scalar(0, ledger, mode=mode, decimal_prec=decimal_prec)
    one = make_scalar(1, ledger, mode=mode, decimal_prec=decimal_prec)
    margins: list[TrackedScalar] = []
    for i in range(n):
        u = [zero] * n
        ui = one / factor.diag[i]
        u[i] = ui
        w = ui * ui
        for r in range(i + 1, n):
            s = zero
            for k, l_rk in factor.offdiag_nz[r]:
                if k >= i:
                    s = s + l_rk * u[k]
            ur = (-s) / factor.diag[r]
            u[r] = ur
            w = w + ur * ur
        margins.append(one / w)
    return margins


def walsh_fourier_clause_eval(
    phi: Sequence[TrackedScalar],
    sin_phi: Sequence[TrackedScalar],
    sigma: Sequence[TrackedScalar],
    weights: Sequence[TrackedScalar],
    ops: SparseOperators,
) -> tuple[TrackedScalar, list[TrackedScalar]]:
    """Compute weighted Walsh-Hadamard potential Phi_WF and exact phi-gradient."""
    n = ops.n
    eighth = ops.eighth
    three = ops.three
    one = ops.one

    total_wf = ops.zero
    dU_dsigma = [ops.zero] * n

    for j, (a, b, c) in enumerate(ops.inc.clauses):
        sa = sigma[a]
        sb = sigma[b]
        sc = sigma[c]
        wj = weights[j]

        sab = sa * sb
        sbc = sb * sc
        sca = sc * sa
        sabc = sab * sc

        # U_j(sigma) = (5 - (sa+sb+sc) + (sab+sbc+sca) + 3*sabc) / 8
        u_num = (
            make_scalar(5, ops.ledger, mode=ops.mode, decimal_prec=ops.decimal_prec)
            - (sa + sb + sc)
            + (sab + sbc + sca)
            + three * sabc
        )
        total_wf = total_wf + wj * (u_num * eighth)

        # Exact partial derivatives w.r.t. each literal slot
        da = (-one + sb + sc + three * sbc) * eighth
        db = (-one + sa + sc + three * sca) * eighth
        dc = (-one + sa + sb + three * sab) * eighth

        dU_dsigma[a] = dU_dsigma[a] + wj * da
        dU_dsigma[b] = dU_dsigma[b] + wj * db
        dU_dsigma[c] = dU_dsigma[c] + wj * dc

    grad_phi = [-(sin_phi[i]) * dU_dsigma[i] for i in range(n)]
    return total_wf, grad_phi


def evaluate_dual_certificate(
    y_cert: Sequence[TrackedScalar],
    s_cert: Sequence[TrackedScalar],
    factor_cert: CholeskyFactor,
    ops: SparseOperators,
    compute_grad_s: bool = True,
) -> tuple[
    TrackedScalar,
    list[TrackedScalar],
    list[TrackedScalar],
    list[TrackedScalar],
    list[TrackedScalar],
]:
    """Evaluate D_spec(y, s), x_dual(y, s), b(y, s), grad_y, and grad_s."""
    n = ops.n
    m = ops.m
    at_y = ops.apply_AT(y_cert)
    b_vec: list[TrackedScalar] = []
    neg_half_b: list[TrackedScalar] = []
    neg_half = make_scalar(-0.5, ops.ledger, mode=ops.mode, decimal_prec=ops.decimal_prec)

    for i in range(n):
        bi = at_y[i] - ops.two * ops.degrees_s[i] - s_cert[i]
        b_vec.append(bi)
        neg_half_b.append(neg_half * bi)

    x_dual = cholesky_solve(factor_cert, neg_half_b)

    # D_spec = m - sum(y) - x_dual^T M_cert x_dual = m - sum(y) - sum_i x_dual_i * (-0.5 * b_i)
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
    return d_spec, x_dual, b_vec, grad_y, grad_s


def threshold_round(x_vals: Sequence[TrackedScalar]) -> list[int]:
    """Direct threshold rounding I[x_i >= 0.5]."""
    return [1 if xi >= 0.5 else 0 for xi in x_vals]


def greedy_conflict_round(
    x_vals: Sequence[TrackedScalar],
    inc: SparseIncidence,
    ledger: BitLedger | None = None,
) -> list[int]:
    """Conflict-aware greedy sweep rounding in descending order of x_i."""
    n = inc.n_vars
    m = inc.m_clauses
    order = sorted(range(n), key=lambda i: (-x_vals[i].value, i))
    x_hat = [0] * n
    if ledger is not None:
        zero_ti = TrackedInt(0, ledger, count_op=False)
        clause_hits_ti: list[TrackedInt] = [zero_ti] * m
        for i in order:
            can_set = True
            for c_idx, coeff in inc.var_clauses[i]:
                if coeff > 1 or clause_hits_ti[c_idx] > 0:
                    can_set = False
                    break
            if can_set:
                x_hat[i] = 1
                for c_idx, coeff in inc.var_clauses[i]:
                    clause_hits_ti[c_idx] = clause_hits_ti[c_idx] + coeff
    else:
        clause_hits = [0] * m
        for i in order:
            can_set = True
            for c_idx, coeff in inc.var_clauses[i]:
                if coeff > 1 or clause_hits[c_idx] > 0:
                    can_set = False
                    break
            if can_set:
                x_hat[i] = 1
                for c_idx, coeff in inc.var_clauses[i]:
                    clause_hits[c_idx] += coeff
    return x_hat


def clamp_scalar(
    val: TrackedScalar,
    bound: TrackedScalar,
) -> TrackedScalar:
    """Symmetric box projection onto [-bound, bound]."""
    if val > bound:
        return bound
    neg_b = -bound
    if val < neg_b:
        return neg_b
    return val


@dataclass(frozen=True)
class LDLTFactor:
    """Square-root-free L D L^T factorization (unit lower-triangular L, diagonal D > 0).

    Eliminates Newton square-root denominator squaring at t=0 in exact rational/float modes.
    """

    size: int
    L: list[list[TrackedScalar]]
    D: tuple[TrackedScalar, ...]
    offdiag_nz: tuple[tuple[tuple[int, TrackedScalar], ...], ...]


def ldlt_factor(
    mat: Sequence[Sequence[TrackedScalar]],
    ledger: BitLedger,
    mode: str = "float64",
    decimal_prec: int = 80,
) -> LDLTFactor | None:
    """Compute square-root-free L D L^T = mat. Returns None if not strictly SPD."""
    n = len(mat)
    zero = make_scalar(0, ledger, mode=mode, decimal_prec=decimal_prec)
    one = make_scalar(1, ledger, mode=mode, decimal_prec=decimal_prec)
    L: list[list[TrackedScalar]] = [[zero] * n for _ in range(n)]
    D: list[TrackedScalar] = []
    offdiag_nz: list[tuple[tuple[int, TrackedScalar], ...]] = []

    for i in range(n):
        row_L = L[i]
        row_mat = mat[i]
        nz_list: list[tuple[int, TrackedScalar]] = []
        for j in range(i):
            s = row_mat[j]
            for k, ljk in offdiag_nz[j]:
                lik = row_L[k]
                if not is_zero_scalar(lik):
                    s = s - (lik * D[k]) * ljk
            val = s / D[j]
            if not is_finite_scalar(val):
                return None
            row_L[j] = val
            if not is_zero_scalar(val):
                nz_list.append((j, val))

        diag_s = row_mat[i]
        for j, lij in nz_list:
            diag_s = diag_s - (lij * lij) * D[j]
        if not is_finite_scalar(diag_s) or not is_pos_scalar(diag_s):
            return None
        row_L[i] = one
        D.append(diag_s)
        offdiag_nz.append(tuple(nz_list))

    return LDLTFactor(
        size=n,
        L=L,
        D=tuple(D),
        offdiag_nz=tuple(offdiag_nz),
    )


def ldlt_solve(factor: LDLTFactor, rhs: Sequence[TrackedScalar]) -> list[TrackedScalar]:
    """Solve (L D L^T) x = rhs without square roots."""
    n = factor.size
    if n == 0:
        return []
    y = list(rhs)
    for i in range(n):
        s = y[i]
        for j, l_ij in factor.offdiag_nz[i]:
            s = s - l_ij * y[j]
        y[i] = s

    x = [y[i] / factor.D[i] for i in range(n)]
    for j in range(n - 1, -1, -1):
        xj = x[j]
        if not is_zero_scalar(xj):
            for k, l_jk in factor.offdiag_nz[j]:
                x[k] = x[k] - l_jk * xj
    return x


@dataclass(frozen=True)
class BareissFactor:
    """Fraction-free Bareiss integer elimination for exact SPD integer matrices M.

    Stores exact integer upper-triangular matrix U and pivot determinants p_k
    bounded by Hadamard's inequality O(n log(n * max|M_ij|)) with zero rational blowup.
    """

    size: int
    U: list[list[TrackedInt]]
    pivots: tuple[TrackedInt, ...]
    det: TrackedInt


def bareiss_spd_factor_int(
    mat_int: Sequence[Sequence[TrackedInt]],
    ledger: BitLedger,
) -> BareissFactor | None:
    """Fraction-free Bareiss elimination on an integer SPD matrix M.

    Every division is exact in Z (proven by Sylvester's determinant identity),
    keeping bit-widths strictly polynomial O(n log(n * ||M||_inf)).
    """
    n = len(mat_int)
    if n == 0:
        one_ti = TrackedInt(1, ledger, count_op=False)
        return BareissFactor(size=0, U=[], pivots=(), det=one_ti)

    U: list[list[TrackedInt]] = [[cell for cell in row] for row in mat_int]
    prev_pivot = TrackedInt(1, ledger, count_op=False)
    pivots: list[TrackedInt] = []

    for k in range(n):
        piv = U[k][k]
        if piv <= 0:
            return None
        pivots.append(piv)
        for i in range(k + 1, n):
            u_ik = U[i][k]
            for j in range(k + 1, n):
                num = piv * U[i][j] - u_ik * U[k][j]
                U[i][j] = num // prev_pivot
            U[i][k] = TrackedInt(0, ledger, count_op=False)
        prev_pivot = piv

    return BareissFactor(
        size=n,
        U=U,
        pivots=tuple(pivots),
        det=pivots[-1],
    )


def bareiss_spd_solve_float64(
    mat_int: Sequence[Sequence[TrackedInt]],
    rhs_float: Sequence[float],
    ledger: BitLedger,
) -> list[float] | None:
    """Solve M x = rhs using exact Bareiss SPD check + bounded float64 LDL^T."""
    bf = bareiss_spd_factor_int(mat_int, ledger)
    if bf is None:
        return None
    n = bf.size
    mat_f = [
        [make_scalar(float(mat_int[i][j].value), ledger, mode="float64") for j in range(n)]
        for i in range(n)
    ]
    fac = ldlt_factor(mat_f, ledger, mode="float64")
    if fac is None:
        return None
    rhs_s = [make_scalar(float(v), ledger, mode="float64") for v in rhs_float]
    sol = ldlt_solve(fac, rhs_s)
    return [float(s.value) for s in sol]
