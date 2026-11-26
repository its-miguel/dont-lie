"""Unit tests for bit-width, dynamic-range, cancellation, and guardrail telemetry."""

from __future__ import annotations

from decimal import Decimal
from fractions import Fraction
import math
import unittest

from monotone_1in3.bitwidth import (
    BitLedger,
    BitWidthExceededError,
    TrackedDecimal,
    TrackedFloat,
    TrackedFraction,
    TrackedInt,
    make_scalar,
    t_acos,
    t_cos,
    t_exp,
    t_fmod_2pi,
    t_log,
    t_pi,
    t_sin,
    t_sqrt,
)
from monotone_1in3.instance import Monotone1in3Instance
from monotone_1in3.primitives import cholesky_factor
from monotone_1in3.solver import SolverConfig, solve_pd_pfgc


class TestBitWidth(unittest.TestCase):
    def test_tracked_int_bit_length_growth_and_guardrail(self) -> None:
        ledger = BitLedger(max_int_bits_limit=16, raise_on_guardrail=True)
        a = TrackedInt(1, ledger)
        for _ in range(15):
            a = a << 1
        self.assertEqual(int(a), 1 << 15)
        self.assertEqual(ledger.max_int_bit_length, 16)
        self.assertEqual(ledger.max_signed_int_bits, 17)
        self.assertEqual(ledger.int_ops, 15)

        with self.assertRaises(BitWidthExceededError):
            _ = a << 1
        self.assertTrue(ledger.guardrail_tripped)

    def test_tracked_float_dynamic_range_cancellation_and_anomalies(self) -> None:
        ledger = BitLedger()
        big = TrackedFloat(2.0**20, ledger)
        small = TrackedFloat(2.0**-10, ledger)
        _ = big + small
        # exp(2^20) = 21, exp(2^-10) = -9 => span = (21 - (-9)) + 53 = 83
        self.assertGreaterEqual(ledger.max_dynamic_range_bits, 83)
        self.assertEqual(ledger.max_float_physical_bits, 64)

        # Catastrophic cancellation: 1.0 - (1.0 - 2^-40)
        x = TrackedFloat(1.0, ledger)
        y = TrackedFloat(1.0 - 2.0**-40, ledger)
        _ = x - y
        self.assertGreaterEqual(ledger.max_cancellation_bits, 40)

        # Subnormal & underflow to zero
        tiny = TrackedFloat(1e-315, ledger)
        self.assertGreaterEqual(ledger.subnormal_count, 1)
        _ = tiny * TrackedFloat(1e-20, ledger)
        self.assertGreaterEqual(ledger.underflow_to_zero_count, 1)

        # Overflow & NaN
        huge = TrackedFloat(1e308, ledger)
        inf_val = huge * TrackedFloat(10.0, ledger)
        self.assertGreaterEqual(ledger.overflow_count, 1)
        _ = inf_val - inf_val
        self.assertGreaterEqual(ledger.nan_count, 1)

    def test_tracked_fraction_exponential_growth_and_limit(self) -> None:
        ledger = BitLedger(max_fraction_bits_limit=512, raise_on_guardrail=True)
        q = TrackedFraction(Fraction(3, 7), ledger)
        # Cubic polynomial iteration x <- 3*x^3 + 1/5 causes rapid bit growth
        tripped = False
        try:
            for _ in range(15):
                q = q * q * q + Fraction(1, 5)
        except BitWidthExceededError:
            tripped = True
        self.assertTrue(tripped)
        self.assertTrue(ledger.guardrail_tripped)
        self.assertGreater(ledger.max_fraction_bits, 512)

    def test_tracked_decimal_high_precision_trig(self) -> None:
        ledger = BitLedger()
        x = TrackedDecimal(Decimal("0.7"), ledger, prec=70)
        s = t_sin(x)
        c = t_cos(x)
        identity = s * s + c * c
        self.assertLess(abs(identity.value - Decimal(1)), Decimal("1e-60"))
        self.assertGreater(ledger.max_float_physical_bits, 200)
        r = t_sqrt(TrackedDecimal(Decimal("2"), ledger, prec=70))
        self.assertLess(abs(r * r - TrackedDecimal(Decimal("2"), ledger, prec=70)).value, Decimal("1e-65"))

    def test_iteration_snapshots(self) -> None:
        ledger = BitLedger()
        ledger.begin_iteration(0)
        x = TrackedFloat(1.5, ledger)
        _ = x * x
        snap = ledger.end_iteration()
        self.assertEqual(snap["iteration"], 0)
        self.assertEqual(snap["iter_ops"], 1)
        self.assertEqual(len(ledger.iteration_bit_history), 1)

    def test_exact_float_cancellation_records_53_bits(self) -> None:
        ledger_sub = BitLedger()
        _ = TrackedFloat(1.0, ledger_sub) - TrackedFloat(1.0, ledger_sub)
        self.assertEqual(ledger_sub.max_cancellation_bits, 53)

        ledger_add = BitLedger()
        _ = TrackedFloat(1.0, ledger_add) + TrackedFloat(-1.0, ledger_add)
        self.assertEqual(ledger_add.max_cancellation_bits, 53)

    def test_decimal_iter_dynamic_range_cancellation_and_tiny_cholesky(self) -> None:
        ledger = BitLedger()
        ledger.begin_iteration(0)
        a = TrackedDecimal(Decimal("1e-100"), ledger, prec=80)
        b = TrackedDecimal(Decimal("1e100"), ledger, prec=80)
        _ = a + b
        snap = ledger.end_iteration()
        self.assertEqual(snap["iter_dynamic_range_bits"], ledger.summary()["max_dynamic_range_bits"])
        self.assertEqual(snap["iter_dynamic_range_bits"], 931)

        # Decimal cancellation tracking (partial and exact)
        _ = TrackedDecimal(Decimal("1e50"), ledger, prec=80) - (
            TrackedDecimal(Decimal("1e50"), ledger, prec=80) - Decimal(1)
        )
        self.assertGreaterEqual(ledger.max_cancellation_bits, 160)

        ledger_exact = BitLedger()
        _ = TrackedDecimal(Decimal("1"), ledger_exact, prec=80) - TrackedDecimal(Decimal("1"), ledger_exact, prec=80)
        self.assertGreaterEqual(ledger_exact.max_cancellation_bits, 266)

        # Sub-float64-underflow Decimal Cholesky (1e-330) must succeed
        ledger_chol = BitLedger()
        tiny = make_scalar(Decimal("1e-330"), ledger_chol, mode="decimal", decimal_prec=80)
        factor = cholesky_factor([[tiny]], ledger_chol, mode="decimal", decimal_prec=80)
        self.assertIsNotNone(factor)
        assert factor is not None
        self.assertLess(abs(factor.diag[0].value - Decimal("1e-165")), Decimal("1e-230"))

    def test_fraction_math_helpers_extreme_scale_guards(self) -> None:
        ledger = BitLedger()
        huge = TrackedFraction(Fraction(10**400), ledger)
        neg_huge = TrackedFraction(Fraction(-10**400), ledger)
        tiny = TrackedFraction(Fraction(1, 10**400), ledger)
        sq_huge = t_sqrt(huge)
        sq_tiny = t_sqrt(tiny)
        self.assertEqual(sq_huge.value, Fraction(10**200))
        self.assertGreater(sq_tiny.value, 0)
        self.assertLess(abs(sq_tiny.value - Fraction(1, 10**200)), Fraction(1, 10**250))

        wrapped = t_fmod_2pi(huge, mode="fraction")
        self.assertGreater(wrapped.value, -Fraction(4))
        self.assertLessEqual(wrapped.value, Fraction(4))
        _ = t_cos(huge)
        _ = t_sin(huge)

        # t_acos extreme-scale guards (Fraction and Decimal)
        self.assertEqual(t_acos(huge).value, Fraction(0))
        self.assertLess(abs(float(t_acos(neg_huge)) - math.pi), 1e-12)
        self.assertLess(abs(float(t_acos(tiny)) - math.pi / 2.0), 1e-12)
        self.assertLess(
            abs(float(t_acos(TrackedFraction(Fraction(1, 3), ledger))) - math.acos(1.0 / 3.0)),
            1e-12,
        )
        dec_huge = TrackedDecimal(Decimal("1e400"), ledger, prec=80)
        dec_neg_huge = TrackedDecimal(Decimal("-1e400"), ledger, prec=80)
        self.assertEqual(t_acos(dec_huge).value, Decimal(0))
        self.assertLess(abs(float(t_acos(dec_neg_huge)) - math.pi), 1e-12)

        # t_log extreme-scale & domain error guards
        self.assertLess(abs(float(t_log(huge)) - 400.0 * math.log(10.0)), 1e-10)
        self.assertLess(abs(float(t_log(tiny)) + 400.0 * math.log(10.0)), 1e-10)
        self.assertEqual(t_log(TrackedFraction(Fraction(1), ledger)).value, Fraction(0))
        with self.assertRaises(ValueError):
            _ = t_log(TrackedFraction(Fraction(0), ledger))
        with self.assertRaises(ValueError):
            _ = t_log(TrackedFraction(Fraction(-1), ledger))

        # t_exp extreme-scale underflow/overflow guards
        self.assertEqual(t_exp(neg_huge).value, Fraction(0))
        self.assertGreaterEqual(ledger.underflow_to_zero_count, 1)
        self.assertEqual(t_exp(tiny).value, Fraction(1))
        exp_huge = t_exp(huge)
        self.assertGreater(exp_huge.value, Fraction(0))
        self.assertGreaterEqual(ledger.overflow_count, 1)
        self.assertLess(abs(float(t_exp(TrackedFraction(Fraction(1), ledger))) - math.e), 1e-12)

    def test_t_fmod_2pi_parity_across_modes(self) -> None:
        wrapped_by_mode: dict[str, list[float]] = {}
        for mode in ("float64", "decimal", "fraction"):
            ledger = BitLedger()
            pi_m = t_pi(ledger, mode=mode, decimal_prec=80)
            inputs = [
                make_scalar(0, ledger, mode=mode, decimal_prec=80),
                make_scalar(1, ledger, mode=mode, decimal_prec=80),
                make_scalar(-1, ledger, mode=mode, decimal_prec=80),
                make_scalar(7, ledger, mode=mode, decimal_prec=80),
                make_scalar(-7, ledger, mode=mode, decimal_prec=80),
                pi_m,
                -pi_m,
            ]
            outputs = []
            for idx, val in enumerate(inputs):
                w = t_fmod_2pi(val, mode=mode, decimal_prec=80)
                self.assertGreater(w.value, -pi_m.value, msg=f"{mode} idx={idx} <= -pi")
                self.assertLessEqual(w.value, pi_m.value, msg=f"{mode} idx={idx} > pi")
                if idx == 0:
                    self.assertEqual(w.value, 0, msg=f"{mode} fmod(0) != 0")
                if idx in (5, 6):
                    self.assertLess(abs(float(w) - float(pi_m)), 1e-12, msg=f"{mode} +-pi wrap")
                outputs.append(float(w))
            wrapped_by_mode[mode] = outputs

        for i in range(len(wrapped_by_mode["float64"])):
            self.assertLess(
                abs(wrapped_by_mode["decimal"][i] - wrapped_by_mode["float64"][i]),
                1e-12,
                msg=f"decimal vs float64 mismatch at idx={i}",
            )
            self.assertLess(
                abs(wrapped_by_mode["fraction"][i] - wrapped_by_mode["float64"][i]),
                1e-12,
                msg=f"fraction vs float64 mismatch at idx={i}",
            )

        frac_ledger = BitLedger()
        pi_q = t_pi(frac_ledger, mode="fraction")
        neg_huge_wrapped = t_fmod_2pi(TrackedFraction(Fraction(-10**400), frac_ledger), mode="fraction")
        self.assertGreater(neg_huge_wrapped.value, -pi_q.value)
        self.assertLessEqual(neg_huge_wrapped.value, pi_q.value)

    def test_solver_x0_parity_single_clause_000(self) -> None:
        inst = Monotone1in3Instance(1, ((0, 0, 0),))
        res_f64 = solve_pd_pfgc(inst, SolverConfig(mode="float64", max_iters=1, max_fraction_bits_limit=None))
        res_dec = solve_pd_pfgc(inst, SolverConfig(mode="decimal", max_iters=1, max_fraction_bits_limit=None))
        res_frac = solve_pd_pfgc(inst, SolverConfig(mode="fraction", max_iters=1, max_fraction_bits_limit=None))

        self.assertLess(abs(res_f64.final_x[0] - 1.0 / 3.0), 1e-12)
        self.assertLess(abs(res_dec.final_x[0] - 1.0 / 3.0), 1e-12)
        self.assertLess(abs(res_frac.final_x[0] - 1.0 / 3.0), 1e-3)
        self.assertLess(abs(res_frac.final_x[0] - res_f64.final_x[0]), 1e-3)


if __name__ == "__main__":
    unittest.main()
