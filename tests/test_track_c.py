"""Unit tests for Track C: Modular F_2 Linear + Bounded Degree-3 Boolean Groebner."""

from __future__ import annotations

import ast
from pathlib import Path
import unittest

from monotone_1in3.generators import (
    generate_3sat_f4,
    generate_planted_f2,
    generate_random_f1,
    generate_tseitin_f3,
)
from monotone_1in3.instance import Monotone1in3Instance
from monotone_1in3.solver import SolverConfig
from monotone_1in3.tracks.track_c_f2_groebner import solve_track_c
from monotone_1in3.verifier import verify_assignment


_FORBIDDEN_IMPORTS = {
    "pysat",
    "z3",
    "ortools",
    "scipy",
    "numpy",
    "pulp",
    "cvxpy",
    "sympy",
    "subprocess",
    "generators",
    "harness",
}


class TestTrackCF2Groebner(unittest.TestCase):
    def test_ast_isolation_and_no_cholesky(self) -> None:
        fpath = (
            Path(__file__).resolve().parents[1]
            / "src"
            / "monotone_1in3"
            / "tracks"
            / "track_c_f2_groebner.py"
        )
        tree = ast.parse(fpath.read_text(encoding="utf-8"), filename=str(fpath))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    root = alias.name.split(".")[0]
                    self.assertNotIn(root, _FORBIDDEN_IMPORTS, msg=f"Imported {alias.name}")
            elif isinstance(node, ast.ImportFrom):
                mod = (node.module or "").split(".")[0]
                self.assertNotIn(mod, _FORBIDDEN_IMPORTS, msg=f"Imported from {node.module}")
                for alias in node.names:
                    self.assertNotIn(
                        alias.name,
                        {"exact_dpll_solve", "cholesky_factor", "cholesky_solve", "cholesky_diag_margins"},
                        msg=f"Forbidden symbol import: {alias.name}",
                    )

    def test_f2_rref_certifies_tseitin_unsat_with_1bit_width(self) -> None:
        for n in (15, 30, 60):
            case = generate_tseitin_f3(n, sat=False, seed=20261124 + n)
            res = solve_track_c(case.instance, SolverConfig(max_iters=50))
            self.assertEqual(res.status, "UNSAT_CERTIFIED", msg=f"Failed Tseitin UNSAT n={n}")
            self.assertGreater(res.dual_certificate_value, 0.0)
            self.assertEqual(res.iterations, 0)
            # Strictly 1-bit F_2 entries, zero rational blowup, zero overflows
            self.assertLessEqual(res.bit_summary["max_int_bit_length"], 1)
            self.assertEqual(res.bit_summary["fraction_ops"], 0)
            self.assertEqual(res.bit_summary["overflow_count"], 0)
            self.assertGreater(res.bit_summary["int_ops"], 0)

    def test_k4_3_and_groebner_unsat_gadgets(self) -> None:
        # K4^3: certified in Stage 2 (degree-2/3 ideal closure) in 0 PD-PFGC iterations
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        res_k4 = solve_track_c(k4, SolverConfig(max_iters=50))
        self.assertEqual(res_k4.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_k4.dual_certificate_value, 0.0)
        self.assertEqual(res_k4.iterations, 0)
        self.assertLessEqual(res_k4.bit_summary["max_int_bit_length"], 1)

        # Repeated literal UNSAT: (0,0,0) and (0,0,1),(1,1,2)
        inst_000 = Monotone1in3Instance(1, ((0, 0, 0),))
        res_000 = solve_track_c(inst_000, SolverConfig(max_iters=20))
        self.assertEqual(res_000.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_000.dual_certificate_value, 0.0)

        dup_chain = Monotone1in3Instance(3, ((0, 0, 1), (1, 1, 2)))
        res_dup = solve_track_c(dup_chain, SolverConfig(max_iters=20))
        self.assertEqual(res_dup.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_dup.dual_certificate_value, 0.0)

    def test_equivalence_plus_quadratic_annihilator_deduction(self) -> None:
        # (0, 1, 2) and (0, 1, 3) => x2 = x3; combined with (2, 3, 4) and x2*x3 = 0 => x2=x3=0, x4=1
        # Adding (4, 5, 6), (4, 5, 7), (5, 6, 7) forces x5=x6=x7=0 contradicting (5,6,7)!
        inst_unsat = Monotone1in3Instance(
            8,
            (
                (0, 1, 2),
                (0, 1, 3),
                (2, 3, 4),
                (4, 5, 6),
                (4, 5, 7),
                (5, 6, 7),
            ),
        )
        res = solve_track_c(inst_unsat, SolverConfig(max_iters=20))
        self.assertEqual(res.status, "UNSAT_CERTIFIED")
        self.assertGreater(res.dual_certificate_value, 0.0)
        self.assertEqual(res.iterations, 0)

        # SAT version without (5, 6, 7): must NOT falsely claim UNSAT, and must find valid SAT
        inst_sat = Monotone1in3Instance(
            8,
            (
                (0, 1, 2),
                (0, 1, 3),
                (2, 3, 4),
                (4, 5, 6),
                (4, 5, 7),
            ),
        )
        res_sat = solve_track_c(inst_sat, SolverConfig(max_iters=50))
        self.assertEqual(res_sat.status, "SAT")
        self.assertIsNotNone(res_sat.assignment)
        assert res_sat.assignment is not None
        self.assertTrue(verify_assignment(inst_sat, res_sat.assignment).is_sat)
        self.assertEqual(res_sat.assignment[2], 0)
        self.assertEqual(res_sat.assignment[3], 0)
        self.assertEqual(res_sat.assignment[4], 1)

    def test_sat_soundness_across_families(self) -> None:
        cases = [
            generate_planted_f2(15, 9, seed=20261124 + 1),
            generate_tseitin_f3(15, sat=True, seed=20261124 + 2),
            generate_3sat_f4(15, sat=True, seed=20261124 + 3),
            generate_random_f1(15, 12, seed=20261124 + 4),
        ]
        for case in cases:
            res = solve_track_c(case.instance, SolverConfig(max_iters=150, record_iter_history=False))
            self.assertNotEqual(res.status, "OVERFLOW")
            if case.ground_truth == "SAT":
                self.assertNotEqual(res.status, "UNSAT_CERTIFIED", msg=f"False UNSAT on {case.instance_id}")
            if res.status == "SAT":
                self.assertIsNotNone(res.assignment)
                assert res.assignment is not None
                self.assertTrue(verify_assignment(case.instance, res.assignment).is_sat)

    def test_edge_cases_and_isolated_vars(self) -> None:
        empty_m = Monotone1in3Instance(3, ())
        r0 = solve_track_c(empty_m)
        self.assertEqual(r0.status, "SAT")
        assert r0.assignment is not None
        self.assertTrue(verify_assignment(empty_m, r0.assignment).is_sat)

        iso = Monotone1in3Instance(5, ((0, 1, 2),))
        r1 = solve_track_c(iso, SolverConfig(max_iters=50))
        self.assertEqual(r1.status, "SAT")
        assert r1.assignment is not None
        self.assertTrue(verify_assignment(iso, r1.assignment).is_sat)


if __name__ == "__main__":
    unittest.main()
