"""Unit tests for R3 generators, gadget truth tables, hygiene invariants, and DPLL agreement."""

from __future__ import annotations

from collections import Counter
import itertools
import unittest

from monotone_1in3.generators import (
    exact_dpll_solve,
    generate_benchmark_suite,
    generate_planted_f2,
)
from monotone_1in3.verifier import verify_assignment


class TestGenerators(unittest.TestCase):
    def test_constant_gadget_truth_table(self) -> None:
        # 4-var (z1, z0, z0p, z0pp) -> unique solution (1, 0, 0, 0)
        clauses = ((0, 1, 2), (0, 1, 3), (0, 2, 3))
        sols = [
            bits
            for bits in itertools.product((0, 1), repeat=4)
            if all(bits[a] + bits[b] + bits[c] == 1 for a, b, c in clauses)
        ]
        self.assertEqual(sols, [(1, 0, 0, 0)])

    def test_schaefer_3or_gadget_truth_table(self) -> None:
        # Variables: l1=0, nl1=1, l2=2, l3=3, nl3=4, z0=5(0), a=6, b=7, c=8, d=9
        # (~l1, a, b), (b, l2, c), (c, d, ~l3) with nl1=1-l1, nl3=1-l3
        valid_triples: set[tuple[int, int, int]] = set()
        for l1, l2, l3 in itertools.product((0, 1), repeat=3):
            nl1 = 1 - l1
            nl3 = 1 - l3
            found = any(
                (nl1 + a + b == 1) and (b + l2 + c == 1) and (c + d + nl3 == 1)
                for a, b, c, d in itertools.product((0, 1), repeat=4)
            )
            if found:
                valid_triples.add((l1, l2, l3))
        expected = set(itertools.product((0, 1), repeat=3)) - {(0, 0, 0)}
        self.assertEqual(valid_triples, expected)

    def test_tseitin_xor_gadgets_truth_tables(self) -> None:
        # deg-3 sigma=1: (a, u, w), (b, u, t), (c, w, t)
        odd_triples = {
            (a, b, c)
            for a, b, c in itertools.product((0, 1), repeat=3)
            if any(
                (a + u + w == 1) and (b + u + t == 1) and (c + w + t == 1)
                for u, w, t in itertools.product((0, 1), repeat=3)
            )
        }
        self.assertEqual(odd_triples, {(1, 1, 1), (1, 0, 0), (0, 1, 0), (0, 0, 1)})

        # deg-3 sigma=0 with z0=0: (a, ba, 0), (ba, u, w), (b, u, t), (c, w, t)
        even_triples = {
            (a, b, c)
            for a, b, c in itertools.product((0, 1), repeat=3)
            if any(
                (a + ba == 1) and (ba + u + w == 1) and (b + u + t == 1) and (c + w + t == 1)
                for ba, u, w, t in itertools.product((0, 1), repeat=4)
            )
        }
        self.assertEqual(even_triples, {(0, 0, 0), (0, 1, 1), (1, 0, 1), (1, 1, 0)})

    def test_determinism_and_full_suite_structure(self) -> None:
        suite1 = generate_benchmark_suite(seed=20261124, fast=False)
        suite2 = generate_benchmark_suite(seed=20261124, fast=False)
        self.assertEqual(len(suite1), 140)
        self.assertEqual(
            [(c.instance_id, c.instance.clauses, c.ground_truth) for c in suite1],
            [(c.instance_id, c.instance.clauses, c.ground_truth) for c in suite2],
        )

        fast_suite = generate_benchmark_suite(seed=20261124, fast=True)
        self.assertEqual(len(fast_suite), 50)

        counts = Counter((c.family, c.n_vars) for c in suite1)
        self.assertEqual(counts[("F1_random", 15)], 20)
        self.assertEqual(counts[("F1_random", 30)], 20)
        self.assertEqual(counts[("F1_random", 60)], 20)
        self.assertEqual(counts[("F2_planted_sat", 15)], 10)
        self.assertEqual(counts[("F2_planted_sat", 30)], 10)
        self.assertEqual(counts[("F2_planted_sat", 60)], 10)
        for fam in ("F3a_tseitin_sat", "F3b_tseitin_unsat", "F4a_3sat_sat"):
            for n in (15, 30, 60):
                self.assertEqual(counts[(fam, n)], 5)
        self.assertEqual(counts[("F4b_3sat_unsat", 60)], 5)

    def test_all_fast_instances_hygiene_and_dpll_ground_truth(self) -> None:
        cases = generate_benchmark_suite(seed=20261124, fast=True)
        for case in cases:
            self.assertIn(case.n_vars, (15, 30, 60))
            self.assertEqual(case.instance.n_vars, case.n_vars)
            ok, errs = case.instance.validate_hygiene()
            self.assertTrue(ok, msg=f"{case.instance_id} failed hygiene: {errs}")
            if case.witness is not None:
                vr = verify_assignment(case.instance, case.witness)
                self.assertTrue(vr.is_sat, msg=f"{case.instance_id} witness invalid")
            sat, _ = exact_dpll_solve(case.instance)
            self.assertEqual(sat, case.ground_truth == "SAT", msg=f"{case.instance_id} DPLL mismatch")

    def test_f2_planted_sat_min_degree_at_least_one(self) -> None:
        # Verify min(deg) >= 1 across all F2 seeds 20261124..20261223 (including 20261146)
        for seed in range(20261124, 20261224):
            case = generate_planted_f2(15, 9, seed)
            deg = [0] * case.n_vars
            for a, b, c in case.instance.clauses:
                deg[a] += 1
                deg[b] += 1
                deg[c] += 1
            self.assertGreaterEqual(min(deg), 1, msg=f"F2 seed={seed} produced isolated variable")

        for n, m in ((15, 12), (30, 19), (30, 22), (60, 38), (60, 41)):
            case = generate_planted_f2(n, m, 20261146)
            deg = [0] * case.n_vars
            for a, b, c in case.instance.clauses:
                deg[a] += 1
                deg[b] += 1
                deg[c] += 1
            self.assertGreaterEqual(min(deg), 1, msg=f"F2 ({n},{m}) produced isolated variable")


if __name__ == "__main__":
    unittest.main()
