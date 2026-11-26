"""Unit and exhaustive small-n tests for the independent deterministic verifier."""

from __future__ import annotations

import itertools
import unittest

from monotone_1in3.instance import Monotone1in3Instance
from monotone_1in3.verifier import verify_assignment, verify_raw


def _brute_force_count(n_vars: int, clauses: tuple[tuple[int, int, int], ...]) -> list[tuple[int, ...]]:
    """Test-only exhaustive 2^n evaluator to cross-check verifier.py."""
    sols: list[tuple[int, ...]] = []
    for bits in itertools.product((0, 1), repeat=n_vars):
        if all(bits[a] + bits[b] + bits[c] == 1 for a, b, c in clauses):
            sols.append(bits)
    return sols


class TestVerifier(unittest.TestCase):
    def test_valid_sat_and_unsat(self) -> None:
        inst = Monotone1in3Instance(4, ((0, 1, 2), (1, 2, 3)))
        res_sat = verify_assignment(inst, [1, 0, 0, 1])
        self.assertTrue(res_sat.is_valid_input)
        self.assertTrue(res_sat.is_sat)
        self.assertEqual(res_sat.satisfied_count, 2)
        self.assertEqual(res_sat.violated_clauses, ())

        res_unsat = verify_assignment(inst, [1, 1, 0, 0])
        self.assertTrue(res_unsat.is_valid_input)
        self.assertFalse(res_unsat.is_sat)
        self.assertEqual(res_unsat.satisfied_count, 1)
        self.assertEqual(len(res_unsat.violated_clauses), 1)
        self.assertEqual(res_unsat.violated_clauses[0], (0, (0, 1, 2), 2))

    def test_rejects_bool_float_wrong_length_and_out_of_domain(self) -> None:
        inst = Monotone1in3Instance(3, ((0, 1, 2),))
        for bad in (
            [True, False, False],
            [1.0, 0, 0],
            [0.33, 0.33, 0.34],
            [1, 0],
            [1, 0, 0, 0],
            [2, 0, -1],
            "100",
        ):
            res = verify_assignment(inst, bad)  # type: ignore[arg-type]
            self.assertFalse(res.is_valid_input, msg=f"Should reject {bad!r}")
            self.assertFalse(res.is_sat, msg=f"Should not be SAT for {bad!r}")

    def test_exhaustive_cross_check_against_bruteforce(self) -> None:
        clauses = ((0, 1, 2), (0, 2, 3), (1, 3, 4), (2, 4, 5))
        inst = Monotone1in3Instance(6, clauses)
        bf_sols = set(_brute_force_count(6, clauses))
        for bits in itertools.product((0, 1), repeat=6):
            vr = verify_assignment(inst, bits)
            self.assertTrue(vr.is_valid_input)
            self.assertEqual(vr.is_sat, bits in bf_sols)

    def test_k4_3_exhaustive_unsat(self) -> None:
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        for bits in itertools.product((0, 1), repeat=4):
            self.assertFalse(verify_assignment(k4, bits).is_sat)

    def test_duplicate_literal_clause_semantics(self) -> None:
        # (0, 0, 1) requires 2*x0 + x1 == 1 -> x0=0, x1=1 only
        res_ok = verify_raw(2, ((0, 0, 1),), (0, 1))
        self.assertTrue(res_ok.is_sat)
        res_bad = verify_raw(2, ((0, 0, 1),), (1, 0))
        self.assertFalse(res_bad.is_sat)
        self.assertEqual(res_bad.violated_clauses[0][2], 2)

    def test_verify_raw_rejects_bool_float_and_invalid_n_vars_and_clauses(self) -> None:
        for n_vars, clauses, assign in (
            (True, ((0, 0, 0),), (1,)),
            (-1, (), ()),
            (3.0, ((0, 1, 2),), (1, 0, 0)),
            (3, ((False, True, 2),), (1, 0, 0)),
            (3, ((0.0, 1, 2),), (1, 0, 0)),
            (3, ("012",), (1, 0, 0)),
        ):
            res = verify_raw(n_vars, clauses, assign)  # type: ignore[arg-type]
            self.assertFalse(res.is_valid_input, msg=f"Should reject {(n_vars, clauses, assign)!r}")
            self.assertFalse(res.is_sat)


if __name__ == "__main__":
    unittest.main()
