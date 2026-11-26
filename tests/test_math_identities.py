"""Algebraic, spectral, and dual-certificate mathematical identity tests for PD-PFGC."""

from __future__ import annotations

import itertools
import math
import random
import unittest

from monotone_1in3.bitwidth import BitLedger, make_scalar, t_cos, t_sin
from monotone_1in3.instance import Monotone1in3Instance, build_incidence
from monotone_1in3.primitives import (
    SparseOperators,
    build_M0,
    build_M_cert,
    cholesky_factor,
    evaluate_dual_certificate,
    walsh_fourier_clause_eval,
)


class TestMathIdentities(unittest.TestCase):
    def test_conflict_matrix_quadratic_identity_on_boolean_vectors(self) -> None:
        clauses = ((0, 1, 2), (1, 2, 3), (0, 3, 4), (2, 2, 4))
        inst = Monotone1in3Instance(5, clauses)
        inc = build_incidence(inst)
        K = inc.compute_k_matrix()
        ledger = BitLedger()
        ops = SparseOperators(inc, ledger)

        rng = random.Random(123)
        for _ in range(30):
            x_int = [rng.randint(0, 1) for _ in range(5)]
            x_s = [make_scalar(v, ledger) for v in x_int]
            ax = [sum(c * x_int[v] for v, c in terms) for terms in inc.clause_terms]
            rhs = sum(v * v for v in ax) - sum(ax)

            kx_dense = sum(x_int[i] * K[i][j] * x_int[j] for i in range(5) for j in range(5))
            kx_sparse = sum(x_int[i] * float(val) for i, val in enumerate(ops.apply_K(x_s)))
            self.assertEqual(kx_dense, rhs)
            self.assertAlmostEqual(kx_sparse, float(rhs), places=12)

    def test_walsh_fourier_clause_polynomial_and_gradient(self) -> None:
        # Test exact 0/1 indicator on all 8 corners of {0,1}^3 and non-negativity on [-1,1]^3
        inst = Monotone1in3Instance(3, ((0, 1, 2),))
        inc = build_incidence(inst)
        ledger = BitLedger()
        ops = SparseOperators(inc, ledger)
        weights = [make_scalar(1.0, ledger)]

        for x0, x1, x2 in itertools.product((0, 1), repeat=3):
            phi_vals = [math.pi if xv == 1 else 0.0 for xv in (x0, x1, x2)]
            phi = [make_scalar(p, ledger) for p in phi_vals]
            sin_phi = [t_sin(p) for p in phi]
            sigma = [t_cos(p) for p in phi]
            u_val, _ = walsh_fourier_clause_eval(phi, sin_phi, sigma, weights, ops)
            expected = 0.0 if (x0 + x1 + x2 == 1) else 1.0
            self.assertAlmostEqual(float(u_val), expected, places=12)

        # Non-negativity on grid in [-1, 1]^3
        grid = [-1.0 + 0.25 * k for k in range(9)]
        for s0, s1, s2 in itertools.product(grid, repeat=3):
            u_grid = (
                5.0 - (s0 + s1 + s2) + (s0 * s1 + s1 * s2 + s2 * s0) + 3.0 * s0 * s1 * s2
            ) / 8.0
            self.assertGreaterEqual(u_grid, -1e-12)

        # Finite-difference gradient check at generic interior point phi
        phi0 = [0.7, 1.4, 2.1]
        phi_s = [make_scalar(p, ledger) for p in phi0]
        _, grad = walsh_fourier_clause_eval(
            phi_s, [t_sin(p) for p in phi_s], [t_cos(p) for p in phi_s], weights, ops
        )
        eps = 1e-6
        for i in range(3):
            p_plus = list(phi0)
            p_minus = list(phi0)
            p_plus[i] += eps
            p_minus[i] -= eps
            sp = [make_scalar(p, ledger) for p in p_plus]
            sm = [make_scalar(p, ledger) for p in p_minus]
            up, _ = walsh_fourier_clause_eval(sp, [t_sin(p) for p in sp], [t_cos(p) for p in sp], weights, ops)
            um, _ = walsh_fourier_clause_eval(sm, [t_sin(p) for p in sm], [t_cos(p) for p in sm], weights, ops)
            fd = (float(up) - float(um)) / (2.0 * eps)
            self.assertAlmostEqual(float(grad[i]), fd, places=6)

    def test_spectral_filter_bounds_and_m0_conditioning(self) -> None:
        clauses = ((0, 1, 2), (1, 2, 3), (2, 3, 4), (0, 4, 5), (1, 3, 5))
        inst = Monotone1in3Instance(6, clauses)
        inc = build_incidence(inst)
        ledger = BitLedger()
        ops = SparseOperators(inc, ledger)
        eta_spec = make_scalar(0.5, ledger)

        # Rayleigh quotient check on F_spec = I - 0.5 * K_norm must lie in [0.5, 1.5]
        rng = random.Random(77)
        for _ in range(50):
            v = [rng.gauss(0.0, 1.0) for _ in range(6)]
            norm_sq = sum(vi * vi for vi in v)
            v_s = [make_scalar(vi, ledger) for vi in v]
            fv = ops.apply_F_spec(v_s, eta_spec)
            rq = sum(v[i] * float(fv[i]) for i in range(6)) / norm_sq
            self.assertGreaterEqual(rq, 0.5 - 1e-10)
            self.assertLessEqual(rq, 1.5 + 1e-10)

        # M0 = I + eta_0 A^T A must have Cholesky factor and Rayleigh quotients in [1, 1 + 9*eta_0*m]
        eta_0 = 1.0
        M0 = build_M0(ops, make_scalar(eta_0, ledger))
        L0 = cholesky_factor(M0, ledger)
        self.assertIsNotNone(L0)
        for _ in range(30):
            v = [rng.gauss(0.0, 1.0) for _ in range(6)]
            norm_sq = sum(vi * vi for vi in v)
            rq_m0 = sum(v[i] * float(M0[i][j]) * v[j] for i in range(6) for j in range(6)) / norm_sq
            self.assertGreaterEqual(rq_m0, 1.0 - 1e-10)
            self.assertLessEqual(rq_m0, 1.0 + 9.0 * eta_0 * len(clauses) + 1e-10)

    def test_k4_3_dual_certificate_and_sat_nonpositivity(self) -> None:
        # K_4^3 UNSAT certification check:
        # At y=0, s=(1+eps)*1 -> D_spec -> 15/16; at y=(-11/9)*1, s=(1+eps)*1 -> D_spec -> 16/9 > 8/9 > 0
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        inc = build_incidence(k4)
        ledger = BitLedger()
        ops = SparseOperators(inc, ledger)
        eps = 1e-6
        s_vec = [make_scalar(1.0 + eps, ledger) for _ in range(4)]
        M_cert = build_M_cert(ops, s_vec)
        L_cert = cholesky_factor(M_cert, ledger)
        self.assertIsNotNone(L_cert)
        assert L_cert is not None

        d0, _, _, _, _ = evaluate_dual_certificate(
            [make_scalar(0.0, ledger) for _ in range(4)], s_vec, L_cert, ops
        )
        self.assertAlmostEqual(float(d0), 15.0 / 16.0, places=5)

        d_opt, _, _, _, _ = evaluate_dual_certificate(
            [make_scalar(-11.0 / 9.0, ledger) for _ in range(4)], s_vec, L_cert, ops
        )
        self.assertAlmostEqual(float(d_opt), 16.0 / 9.0, places=5)
        self.assertGreater(float(d_opt), 8.0 / 9.0)

        # On a known SAT instance, weak duality forces D_spec <= 0 for every valid PD s
        sat_inst = Monotone1in3Instance(4, ((0, 1, 2), (1, 2, 3)))
        sat_inc = build_incidence(sat_inst)
        sat_ops = SparseOperators(sat_inc, ledger)
        s_sat = [make_scalar(d + 0.5, ledger) for d in sat_inc.degrees]
        L_sat = cholesky_factor(build_M_cert(sat_ops, s_sat), ledger)
        assert L_sat is not None
        d_sat, _, _, _, _ = evaluate_dual_certificate(
            [make_scalar(1.5, ledger), make_scalar(-0.7, ledger)], s_sat, L_sat, sat_ops
        )
        self.assertLessEqual(float(d_sat), 1e-12)


if __name__ == "__main__":
    unittest.main()
