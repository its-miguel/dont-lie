"""Unit tests for square-root-free LDL^T and fraction-free Bareiss elimination."""

from __future__ import annotations

import unittest

from monotone_1in3.bitwidth import BitLedger, TrackedInt, make_scalar
from monotone_1in3.instance import Monotone1in3Instance, build_incidence
from monotone_1in3.primitives import (
    SparseOperators,
    bareiss_spd_factor_int,
    bareiss_spd_solve_float64,
    build_M0,
    ldlt_factor,
    ldlt_solve,
)


class TestLDLTAndBareiss(unittest.TestCase):
    """Verify t=0 bit-width blowup is eliminated by LDL^T and Bareiss elimination."""

    def _k4_instance(self) -> Monotone1in3Instance:
        return Monotone1in3Instance(
            n_vars=4,
            clauses=((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)),
            metadata={"name": "K4^3"},
        )

    def test_ldlt_fraction_no_blowup_on_k4(self) -> None:
        inst = self._k4_instance()
        inc = build_incidence(inst)
        ledger = BitLedger(max_fraction_bits_limit=256, raise_on_guardrail=True)
        # Build M0 = I + A^T A directly without calling t_sqrt(D_K)
        n = inst.n_vars
        zero = make_scalar(0, ledger, mode="fraction")
        one = make_scalar(1, ledger, mode="fraction")
        m0 = [[one if i == j else zero for j in range(n)] for i in range(n)]
        for terms in inc.clause_terms:
            for i, ci in terms:
                ci_s = make_scalar(ci, ledger, mode="fraction")
                for j, cj in terms:
                    cj_s = make_scalar(cj, ledger, mode="fraction")
                    m0[i][j] = m0[i][j] + ci_s * cj_s
        fac = ldlt_factor(m0, ledger, mode="fraction")
        self.assertIsNotNone(fac)
        assert fac is not None
        rhs = [make_scalar(i + 1, ledger, mode="fraction") for i in range(n)]
        sol = ldlt_solve(fac, rhs)
        # Verify M0 * sol == rhs exactly
        for i in range(n):
            lhs = zero
            for j in range(n):
                lhs = lhs + m0[i][j] * sol[j]
            self.assertEqual(lhs.value, rhs[i].value)
        summary = ledger.summary()
        self.assertFalse(summary["guardrail_tripped"])
        self.assertLessEqual(summary["max_fraction_bits"], 64)

    def test_bareiss_exact_spd_on_k4(self) -> None:
        inst = self._k4_instance()
        inc = build_incidence(inst)
        ledger = BitLedger(max_int_bits_limit=128, raise_on_guardrail=True)
        ops = SparseOperators(inc, ledger, mode="float64")
        one_ti = TrackedInt(1, ledger, count_op=False)
        m0_int = [
            [
                (ops.ata_int[i][j] + one_ti) if i == j else ops.ata_int[i][j]
                for j in range(inst.n_vars)
            ]
            for i in range(inst.n_vars)
        ]
        bf = bareiss_spd_factor_int(m0_int, ledger)
        self.assertIsNotNone(bf)
        assert bf is not None
        self.assertGreater(bf.det.value, 0)
        sol = bareiss_spd_solve_float64(m0_int, [1.0, 2.0, 3.0, 4.0], ledger)
        self.assertIsNotNone(sol)
        assert sol is not None
        for i in range(inst.n_vars):
            lhs = sum(m0_int[i][j].value * sol[j] for j in range(inst.n_vars))
            self.assertAlmostEqual(lhs, float(i + 1), places=10)
        summary = ledger.summary()
        self.assertFalse(summary["guardrail_tripped"])
        self.assertLessEqual(summary["max_int_bit_length"], 32)


if __name__ == "__main__":
    unittest.main()
