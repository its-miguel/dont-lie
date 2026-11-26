"""Unit tests for Track D: Single-Pass Primal-Dual Marginals & Unit-Collapse Decimation."""

from __future__ import annotations

import ast
import math
from pathlib import Path
import unittest

from monotone_1in3.bitwidth import BitLedger, make_scalar
from monotone_1in3.generators import (
    generate_planted_f2,
    generate_random_f1,
    generate_tseitin_f3,
)
from monotone_1in3.instance import Monotone1in3Instance, build_incidence
from monotone_1in3.primitives import SparseOperators, build_M_cert, ldlt_factor
from monotone_1in3.solver import SolverConfig
from monotone_1in3.tracks.track_d_decimation import (
    _evaluate_dual_certificate_ldlt,
    solve_track_d,
    unit_collapse_propagate,
)
from monotone_1in3.verifier import verify_assignment


_FORBIDDEN_IMPORTS = {
    "numpy",
    "scipy",
    "z3",
    "pysat",
    "pulp",
    "ortools",
    "cvxpy",
    "sympy",
    "subprocess",
    "generators",
    "harness",
}


class TestTrackDUnitCollapse(unittest.TestCase):
    def test_unit_collapse_one_forces_zeros(self) -> None:
        inst = Monotone1in3Instance(4, ((0, 1, 2), (2, 3, 1)))
        inc = build_incidence(inst)
        fixed: list[int | None] = [1, None, None, None]
        ok = unit_collapse_propagate(fixed, inc, seed_vars=(0,))
        self.assertTrue(ok)
        # x0=1 => x1=0, x2=0; then clause (2,3,1) has x1=0, x2=0 => x3=1
        self.assertEqual(fixed, [1, 0, 0, 1])

    def test_unit_collapse_two_zeros_forces_one(self) -> None:
        inst = Monotone1in3Instance(3, ((0, 1, 2),))
        inc = build_incidence(inst)
        fixed: list[int | None] = [0, 0, None]
        ok = unit_collapse_propagate(fixed, inc, seed_vars=(0, 1))
        self.assertTrue(ok)
        self.assertEqual(fixed, [0, 0, 1])

    def test_unit_collapse_local_contradictions(self) -> None:
        inst = Monotone1in3Instance(3, ((0, 1, 2),))
        inc = build_incidence(inst)
        # Two 1s
        f_two_ones: list[int | None] = [1, 1, None]
        self.assertFalse(unit_collapse_propagate(f_two_ones, inc, seed_vars=(0, 1)))
        # Three 0s
        f_three_zeros: list[int | None] = [0, 0, 0]
        self.assertFalse(unit_collapse_propagate(f_three_zeros, inc, seed_vars=(0, 1, 2)))

    def test_repeated_literals_initial_forced(self) -> None:
        # (0, 0, 1) forces x0 = 0, x1 = 1
        inst_aab = Monotone1in3Instance(2, ((0, 0, 1),))
        res_aab = solve_track_d(inst_aab)
        self.assertEqual(res_aab.status, "SAT")
        self.assertEqual(res_aab.assignment, (0, 1))
        self.assertTrue(verify_assignment(inst_aab, res_aab.assignment).is_sat)

        # (0, 0, 0) is immediately UNSAT
        inst_aaa = Monotone1in3Instance(1, ((0, 0, 0),))
        res_aaa = solve_track_d(inst_aaa)
        self.assertEqual(res_aaa.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_aaa.dual_certificate_value, 0.0)


class TestTrackDSoundnessAndCertificates(unittest.TestCase):
    def test_root_unsat_certification_soundness(self) -> None:
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        deg0_k4 = Monotone1in3Instance(6, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        dup_chain = Monotone1in3Instance(3, ((0, 0, 1), (1, 1, 2)))
        f2 = generate_planted_f2(15, 9, seed=20261124 + 7).instance
        f2_k4 = Monotone1in3Instance(
            19, f2.clauses + ((15, 16, 17), (15, 16, 18), (15, 17, 18), (16, 17, 18))
        )
        for name, inst in (
            ("k4", k4),
            ("deg0_k4", deg0_k4),
            ("dup_chain", dup_chain),
            ("f2_k4", f2_k4),
        ):
            res = solve_track_d(inst)
            self.assertEqual(res.status, "UNSAT_CERTIFIED", msg=f"{name} expected UNSAT_CERTIFIED")
            self.assertGreater(res.dual_certificate_value, 0.0)

    def test_ldlt_dual_certificate_evaluator_on_k4(self) -> None:
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        inc = build_incidence(k4)
        ledger = BitLedger()
        ops = SparseOperators(inc, ledger, mode="float64")
        y_cert = [make_scalar(0.0, ledger) for _ in range(4)]
        s_cert = [make_scalar(float(d) + 2.0 * (2.0**-20), ledger) for d in inc.degrees]
        fac = ldlt_factor(build_M_cert(ops, s_cert), ledger, mode="float64")
        self.assertIsNotNone(fac)
        assert fac is not None
        d_spec, x_dual, grad_y, grad_s = _evaluate_dual_certificate_ldlt(
            y_cert, s_cert, fac, ops, compute_grad_s=True
        )
        self.assertEqual(len(x_dual), 4)
        self.assertEqual(len(grad_y), 4)
        self.assertEqual(len(grad_s), 4)
        self.assertTrue(math.isfinite(float(d_spec)))

    def test_speculative_restart_never_claims_false_unsat_on_sat(self) -> None:
        # Test on multiple SAT families including tight max_iters=1 (must be SAT or UNRESOLVED, never UNSAT)
        sat_instances = [
            generate_planted_f2(15, 9, seed=20261124 + 1).instance,
            generate_planted_f2(30, 18, seed=20261124 + 2).instance,
            generate_tseitin_f3(30, sat=True, seed=20261124 + 3).instance,
        ]
        for inst in sat_instances:
            res_tight = solve_track_d(inst, SolverConfig(max_iters=1, record_iter_history=False))
            self.assertNotEqual(res_tight.status, "UNSAT_CERTIFIED")
            if res_tight.status == "SAT":
                assert res_tight.assignment is not None
                self.assertTrue(verify_assignment(inst, res_tight.assignment).is_sat)

            res_full = solve_track_d(inst, SolverConfig(record_iter_history=False))
            self.assertEqual(res_full.status, "SAT")
            assert res_full.assignment is not None
            self.assertTrue(verify_assignment(inst, res_full.assignment).is_sat)

    def test_trivial_edge_cases(self) -> None:
        inst_empty = Monotone1in3Instance(3, ())
        res_empty = solve_track_d(inst_empty)
        self.assertEqual(res_empty.status, "SAT")
        self.assertEqual(res_empty.assignment, (0, 0, 0))

        inst_isolated = Monotone1in3Instance(4, ((0, 1, 2),))
        res_iso = solve_track_d(inst_isolated)
        self.assertEqual(res_iso.status, "SAT")
        assert res_iso.assignment is not None
        self.assertTrue(verify_assignment(inst_isolated, res_iso.assignment).is_sat)


class TestTrackDBitWidthAndIsolation(unittest.TestCase):
    def test_bitwidth_bounds_and_telemetry(self) -> None:
        case = generate_random_f1(30, 18, seed=20261124 + 11)
        res = solve_track_d(case.instance, SolverConfig(record_iter_history=False))
        bs = res.bit_summary
        self.assertEqual(bs["overflow_count"], 0)
        self.assertEqual(bs["nan_count"], 0)
        self.assertFalse(bs["guardrail_tripped"])
        self.assertGreater(bs["int_ops"], 0)
        theo_int_bound = math.ceil(math.log2(9 * case.m_clauses + 1))
        self.assertLessEqual(bs["max_int_bit_length"], theo_int_bound)
        if bs["max_float_exp"] is not None:
            self.assertLess(bs["max_float_exp"], 64)

    def test_bitwidth_guardrail_overflow(self) -> None:
        case = generate_planted_f2(15, 9, seed=20261124 + 5)
        res = solve_track_d(
            case.instance,
            SolverConfig(max_int_bits_limit=1, record_iter_history=False),
        )
        self.assertEqual(res.status, "OVERFLOW")
        self.assertTrue(res.bit_summary["guardrail_tripped"])

    def test_ast_isolation_and_no_recursion_or_cholesky(self) -> None:
        track_path = (
            Path(__file__).resolve().parents[1]
            / "src"
            / "monotone_1in3"
            / "tracks"
            / "track_d_decimation.py"
        )
        source = track_path.read_text(encoding="utf-8")
        tree = ast.parse(source, filename=str(track_path))

        uses_ldlt_factor = False
        uses_ldlt_solve = False

        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    root = alias.name.split(".")[0]
                    self.assertNotIn(root, _FORBIDDEN_IMPORTS)
            elif isinstance(node, ast.ImportFrom):
                mod_parts = (node.module or "").split(".")
                for part in mod_parts:
                    self.assertNotIn(part, _FORBIDDEN_IMPORTS)
                for alias in node.names:
                    self.assertNotIn(alias.name, {"cholesky_factor", "cholesky_solve", "exact_dpll_solve"})
                    if alias.name == "ldlt_factor":
                        uses_ldlt_factor = True
                    if alias.name == "ldlt_solve":
                        uses_ldlt_solve = True
            elif isinstance(node, ast.FunctionDef):
                # Ensure no direct self-recursion anywhere in Track D
                fname = node.name
                for sub in ast.walk(node):
                    if isinstance(sub, ast.Call) and isinstance(sub.func, ast.Name):
                        self.assertNotEqual(
                            sub.func.id,
                            fname,
                            msg=f"Direct recursion detected in {fname}",
                        )

        self.assertTrue(uses_ldlt_factor, "track_d_decimation.py must use ldlt_factor")
        self.assertTrue(uses_ldlt_solve, "track_d_decimation.py must use ldlt_solve")


if __name__ == "__main__":
    unittest.main()
