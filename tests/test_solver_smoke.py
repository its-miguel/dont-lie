"""End-to-end solver smoke tests, precision escalation tests, and AST isolation audits."""

from __future__ import annotations

import ast
from pathlib import Path
import unittest

from monotone_1in3.generators import generate_planted_f2
from monotone_1in3.instance import Monotone1in3Instance
from monotone_1in3.solver import SolverConfig, solve_pd_pfgc
from monotone_1in3.verifier import verify_assignment


_FORBIDDEN_SOLVER_IMPORTS = {
    "pysat",
    "z3",
    "ortools",
    "scipy",
    "pulp",
    "cvxpy",
    "sympy",
    "subprocess",
    "generators",
    "harness",
}


class TestSolverSmokeAndIsolation(unittest.TestCase):
    def test_ast_isolation_no_external_or_oracle_imports(self) -> None:
        pkg_dir = Path(__file__).resolve().parents[1] / "src" / "monotone_1in3"
        isolated_files = ("instance.py", "verifier.py", "bitwidth.py", "primitives.py", "solver.py")
        for fname in isolated_files:
            fpath = pkg_dir / fname
            tree = ast.parse(fpath.read_text(encoding="utf-8"), filename=str(fpath))
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    for alias in node.names:
                        root = alias.name.split(".")[0]
                        self.assertNotIn(root, _FORBIDDEN_SOLVER_IMPORTS, msg=f"{fname} imported {alias.name}")
                elif isinstance(node, ast.ImportFrom):
                    mod = (node.module or "").split(".")[0]
                    self.assertNotIn(mod, _FORBIDDEN_SOLVER_IMPORTS, msg=f"{fname} imported from {node.module}")
                    for alias in node.names:
                        self.assertNotEqual(alias.name, "exact_dpll_solve")

    def test_small_sat_and_isolated_variables(self) -> None:
        # Variable 3 is degree-0 isolated variable (tests zero-degree safety)
        inst = Monotone1in3Instance(4, ((0, 1, 2),))
        res = solve_pd_pfgc(inst, SolverConfig(max_iters=100))
        self.assertEqual(res.status, "SAT")
        self.assertIsNotNone(res.assignment)
        assert res.assignment is not None
        vr = verify_assignment(inst, res.assignment)
        self.assertTrue(vr.is_sat)
        self.assertGreater(res.bit_summary["float_ops"], 0)
        self.assertGreater(res.bit_summary["max_dynamic_range_bits"], 0)

    def test_duplicate_literal_clause_forced_zero(self) -> None:
        # (0, 0, 1) -> x0 = 0, x1 = 1; (A^T A)_00 = 4 -> max_int_bit_length >= 3
        inst = Monotone1in3Instance(2, ((0, 0, 1),))
        res = solve_pd_pfgc(inst, SolverConfig(max_iters=100))
        self.assertEqual(res.status, "SAT")
        self.assertEqual(res.assignment, (0, 1))
        self.assertGreaterEqual(res.bit_summary["max_int_bit_length"], 3)

    def test_k4_3_certified_unsat_and_precision_modes(self) -> None:
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        res_f64 = solve_pd_pfgc(k4, SolverConfig(max_iters=50, dual_update_interval=1))
        self.assertEqual(res_f64.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_f64.dual_certificate_value, 0.0)

        res_dec = solve_pd_pfgc(
            k4, SolverConfig(max_iters=20, mode="decimal", decimal_prec=60, dual_update_interval=1)
        )
        self.assertEqual(res_dec.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_dec.bit_summary["decimal_ops"], 0)
        self.assertGreater(res_dec.bit_summary["max_float_physical_bits"], 180)

        # Fraction mode with small bit-width guardrail demonstrates rational blowup detection
        res_frac = solve_pd_pfgc(
            k4,
            SolverConfig(
                max_iters=20,
                mode="fraction",
                max_fraction_bits_limit=512,
                dual_update_interval=1,
                record_iter_history=False,
            ),
        )
        self.assertIn(res_frac.status, ("OVERFLOW", "UNSAT_CERTIFIED"))
        self.assertGreater(res_frac.bit_summary["fraction_ops"], 0)

    def test_planted_n15_smoke(self) -> None:
        case = generate_planted_f2(15, 9, seed=20261124 + 7)
        res = solve_pd_pfgc(case.instance, SolverConfig(max_iters=300))
        self.assertEqual(res.status, "SAT")
        assert res.assignment is not None
        self.assertTrue(verify_assignment(case.instance, res.assignment).is_sat)

    def test_dual_certificate_on_padded_disconnected_dup_and_high_degree_unsat(self) -> None:
        deg0_k43 = Monotone1in3Instance(6, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        disconn = Monotone1in3Instance(7, ((0, 1, 2), (3, 4, 5), (3, 4, 6), (3, 5, 6), (4, 5, 6)))
        f2 = generate_planted_f2(15, 9, seed=20261124 + 7).instance
        f2_k43 = Monotone1in3Instance(
            19, f2.clauses + ((15, 16, 17), (15, 16, 18), (15, 17, 18), (16, 17, 18))
        )
        dup_chain = Monotone1in3Instance(3, ((0, 0, 1), (1, 1, 2)))
        star_d0_260 = Monotone1in3Instance(
            5, ((0, 1, 2),) * 260 + ((1, 2, 3), (1, 2, 4), (1, 3, 4), (2, 3, 4))
        )

        for name, inst in (
            ("deg0_k43_unsat", deg0_k43),
            ("disconn_sat_unsat", disconn),
            ("F2_plus_K43_unsat", f2_k43),
            ("dup_lit_unsat_chain", dup_chain),
            ("star_d0_260", star_d0_260),
        ):
            res = solve_pd_pfgc(inst, SolverConfig(max_iters=300))
            self.assertEqual(res.status, "UNSAT_CERTIFIED", msg=f"{name} failed UNSAT cert")
            self.assertGreater(res.dual_certificate_value, 0.0)
        res_star = solve_pd_pfgc(star_d0_260, SolverConfig(max_iters=300))
        self.assertGreater(
            res_star.max_kappa2_cert_bound,
            (18.0 * star_d0_260.m_clauses + 256.0) / (2.0**-20),
        )

    def test_x0_parity_across_modes_on_000_and_012(self) -> None:
        inst_000 = Monotone1in3Instance(1, ((0, 0, 0),))
        inst_012 = Monotone1in3Instance(3, ((0, 1, 2),))
        for inst, check_sat in ((inst_000, False), (inst_012, True)):
            res_f64 = solve_pd_pfgc(
                inst, SolverConfig(mode="float64", max_iters=1, max_fraction_bits_limit=None)
            )
            res_dec = solve_pd_pfgc(
                inst, SolverConfig(mode="decimal", max_iters=1, max_fraction_bits_limit=None)
            )
            res_frac = solve_pd_pfgc(
                inst, SolverConfig(mode="fraction", max_iters=1, max_fraction_bits_limit=None)
            )
            for i in range(inst.n_vars):
                self.assertLess(abs(res_frac.final_x[i] - res_f64.final_x[i]), 1e-4)
                self.assertLess(abs(res_frac.final_x[i] - res_dec.final_x[i]), 1e-4)
            if check_sat:
                self.assertEqual(res_frac.status, "SAT")
                assert res_frac.assignment is not None
                self.assertTrue(verify_assignment(inst, res_frac.assignment).is_sat)
            else:
                self.assertLess(res_frac.primal_res_inf, 1e-3)

    def test_fraction_mode_guardrail_on_000(self) -> None:
        inst_000 = Monotone1in3Instance(1, ((0, 0, 0),))
        for limit in (512, 4096):
            res = solve_pd_pfgc(
                inst_000,
                SolverConfig(
                    mode="fraction",
                    max_iters=3,
                    max_fraction_bits_limit=limit,
                    record_iter_history=False,
                ),
            )
            self.assertEqual(res.status, "OVERFLOW")
            self.assertTrue(res.bit_summary["guardrail_tripped"])
            self.assertGreater(res.bit_summary["max_fraction_bits"], limit)


if __name__ == "__main__":
    unittest.main()
