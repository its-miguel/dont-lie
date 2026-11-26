"""Unit tests for Track B: Symplectic Störmer-Verlet Integrator + Polyrhythmic Phase-Kick Annealing."""

from __future__ import annotations

import ast
import math
from pathlib import Path
import unittest

from monotone_1in3.generators import generate_planted_f2, generate_tseitin_f3
from monotone_1in3.instance import Monotone1in3Instance
from monotone_1in3.solver import SolverConfig
from monotone_1in3.tracks.track_b_symplectic import (
    _compute_hamiltonian_grad,
    _deterministic_1flip_polish,
    _walsh_sign,
    solve_track_b,
)
from monotone_1in3.verifier import verify_assignment


_FORBIDDEN_SOLVER_IMPORTS = {
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


class TestTrackBSymplectic(unittest.TestCase):
    def test_ast_isolation_no_external_or_oracle_imports(self) -> None:
        fpath = (
            Path(__file__).resolve().parents[1]
            / "src"
            / "monotone_1in3"
            / "tracks"
            / "track_b_symplectic.py"
        )
        tree = ast.parse(fpath.read_text(encoding="utf-8"), filename=str(fpath))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    root = alias.name.split(".")[0]
                    self.assertNotIn(root, _FORBIDDEN_SOLVER_IMPORTS, msg=f"Imported {alias.name}")
            elif isinstance(node, ast.ImportFrom):
                mod = (node.module or "").split(".")[0]
                self.assertNotIn(mod, _FORBIDDEN_SOLVER_IMPORTS, msg=f"Imported from {node.module}")
                for alias in node.names:
                    self.assertNotEqual(alias.name, "exact_dpll_solve")

    def test_walsh_sign_and_hamiltonian_grad_stability(self) -> None:
        # Walsh-Hadamard characters are strictly in {-1.0, +1.0}
        for a in range(8):
            for b in range(8):
                self.assertIn(_walsh_sign(a, b), (-1.0, 1.0))

        # Verify finite, bounded gradient on a frustrated 1/3 symmetric configuration
        from monotone_1in3.instance import build_incidence

        inst = Monotone1in3Instance(4, ((0, 1, 2), (1, 2, 3), (0, 2, 3)))
        inc = build_incidence(inst)
        phi_13 = [math.acos(1.0 / 3.0)] * 4
        x, r, grad, res_inf, res_l2, igap = _compute_hamiltonian_grad(
            phi_13,
            [0.0] * 3,
            [1.0] * 3,
            inc,
            rho=1.0,
            alpha_k=0.5,
            gamma_wf=1.0,
            gamma_beat=0.5,
            beta_t=0.25,
        )
        self.assertTrue(all(math.isfinite(g) for g in grad))
        self.assertLess(res_inf, 1e-12)
        self.assertAlmostEqual(igap, 1.0 / 3.0, places=6)

    def test_symplectic_step_stability_and_small_sat(self) -> None:
        # Variable 3 is isolated (degree 0)
        inst = Monotone1in3Instance(4, ((0, 1, 2),))
        res = solve_track_b(inst, SolverConfig(max_iters=100))
        self.assertEqual(res.status, "SAT")
        self.assertIsNotNone(res.assignment)
        assert res.assignment is not None
        self.assertTrue(verify_assignment(inst, res.assignment).is_sat)
        self.assertEqual(res.bit_summary["overflow_count"], 0)
        self.assertEqual(res.bit_summary["nan_count"], 0)
        self.assertGreater(res.bit_summary["float_ops"], 0)

    def test_duplicate_literal_clause_and_int_bit_tracking(self) -> None:
        # (0, 0, 1) -> x0=0, x1=1; (A^T A)_00 = 4 -> max_int_bit_length >= 3
        inst = Monotone1in3Instance(2, ((0, 0, 1),))
        res = solve_track_b(inst, SolverConfig(max_iters=100))
        self.assertEqual(res.status, "SAT")
        self.assertEqual(res.assignment, (0, 1))
        self.assertGreaterEqual(res.bit_summary["max_int_bit_length"], 3)

    def test_phase_kick_escape_on_frustrated_sat_instances(self) -> None:
        # Planted SAT n=30 and Tseitin SAT n=30 both test escaping 1/3 / 0.5 basins
        f2_case = generate_planted_f2(30, 18, seed=20261124 + 5)
        res_f2 = solve_track_b(f2_case.instance, SolverConfig(max_time_sec=None, record_iter_history=False))
        self.assertEqual(res_f2.status, "SAT")
        assert res_f2.assignment is not None
        self.assertTrue(verify_assignment(f2_case.instance, res_f2.assignment).is_sat)

        f3_case = generate_tseitin_f3(30, sat=True, seed=20261124 + 3)
        res_f3 = solve_track_b(f3_case.instance, SolverConfig(max_time_sec=None, record_iter_history=False))
        self.assertEqual(res_f3.status, "SAT")
        assert res_f3.assignment is not None
        self.assertTrue(verify_assignment(f3_case.instance, res_f3.assignment).is_sat)

    def test_k4_3_and_padded_unsat_ldlt_certification(self) -> None:
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        res = solve_track_b(k4, SolverConfig(max_iters=100, dual_update_interval=1))
        self.assertEqual(res.status, "UNSAT_CERTIFIED")
        self.assertGreater(res.dual_certificate_value, 0.0)
        self.assertEqual(res.bit_summary["overflow_count"], 0)

        deg0_k43 = Monotone1in3Instance(6, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        res_pad = solve_track_b(deg0_k43, SolverConfig(max_iters=200, dual_update_interval=2))
        self.assertEqual(res_pad.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_pad.dual_certificate_value, 0.0)

    def test_deterministic_1flip_polish_monotone(self) -> None:
        from monotone_1in3.instance import build_incidence

        inst = Monotone1in3Instance(4, ((0, 1, 2), (1, 2, 3)))
        inc = build_incidence(inst)
        # (0, 0, 0, 0) has 2 violations; flipping var 1 -> (0, 1, 0, 0) solves both!
        polished, vcount, vclauses = _deterministic_1flip_polish(
            [0, 0, 0, 0], [0.2, 0.8, 0.2, 0.2], [1.0, 1.0], inc, max_steps=10
        )
        self.assertEqual(vcount, 0)
        self.assertEqual(vclauses, [])
        self.assertTrue(verify_assignment(inst, polished).is_sat)

    def test_bitwidth_bounds_and_guardrail(self) -> None:
        inst = Monotone1in3Instance(3, ((0, 1, 2),))
        # Tight int guardrail of 0 bits must cleanly trigger OVERFLOW
        res_ovf = solve_track_b(inst, SolverConfig(max_iters=10, max_int_bits_limit=0))
        self.assertEqual(res_ovf.status, "OVERFLOW")
        self.assertTrue(res_ovf.bit_summary["guardrail_tripped"])

        # Normal run keeps max_int_bit_length <= ceil(log2(9m + 1)) and bounded float exp
        f2_case = generate_planted_f2(15, 9, seed=20261124 + 1)
        res = solve_track_b(f2_case.instance, SolverConfig(max_iters=200))
        bs = res.bit_summary
        self.assertLessEqual(bs["max_int_bit_length"], math.ceil(math.log2(9 * f2_case.m_clauses + 1)))
        self.assertIsNotNone(bs["max_float_exp"])
        self.assertLess(bs["max_float_exp"], 64)
        self.assertEqual(bs["overflow_count"], 0)
        self.assertEqual(bs["nan_count"], 0)

    def test_trivial_edge_cases(self) -> None:
        empty_clauses = Monotone1in3Instance(3, ())
        res_sat = solve_track_b(empty_clauses)
        self.assertEqual(res_sat.status, "SAT")
        self.assertEqual(res_sat.assignment, (0, 0, 0))


if __name__ == "__main__":
    unittest.main()
