"""Unit tests for Track A (Sparse Degree-3 / Local Clique SoS & RLT Lift)."""

from __future__ import annotations

import ast
from pathlib import Path
import unittest

from monotone_1in3.generators import generate_planted_f2
from monotone_1in3.instance import Monotone1in3Instance
from monotone_1in3.solver import SolverConfig
from monotone_1in3.tracks.track_a_sos_rlt import solve_track_a
from monotone_1in3.verifier import verify_assignment

_FORBIDDEN_IMPORTS = {
    "numpy",
    "scipy",
    "z3",
    "pysat",
    "pulp",
    "milp",
    "ortools",
    "cvxpy",
    "sympy",
    "subprocess",
    "generators",
    "harness",
}


class TestTrackASoSRLT(unittest.TestCase):
    def test_ast_isolation_track_a(self) -> None:
        fpath = (
            Path(__file__).resolve().parents[1]
            / "src"
            / "monotone_1in3"
            / "tracks"
            / "track_a_sos_rlt.py"
        )
        tree = ast.parse(fpath.read_text(encoding="utf-8"), filename=str(fpath))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    root = alias.name.split(".")[0]
                    self.assertNotIn(root, _FORBIDDEN_IMPORTS, msg=f"Forbidden import: {alias.name}")
            elif isinstance(node, ast.ImportFrom):
                mod = (node.module or "").split(".")[0]
                self.assertNotIn(mod, _FORBIDDEN_IMPORTS, msg=f"Forbidden import from: {node.module}")
                for alias in node.names:
                    self.assertNotEqual(alias.name, "exact_dpll_solve")

    def test_trivial_edge_cases(self) -> None:
        inst_empty_m = Monotone1in3Instance(3, ())
        res_m = solve_track_a(inst_empty_m)
        self.assertEqual(res_m.status, "SAT")
        assert res_m.assignment is not None
        self.assertTrue(verify_assignment(inst_empty_m, res_m.assignment).is_sat)

        inst_dup0 = Monotone1in3Instance(1, ((0, 0, 0),))
        res_0 = solve_track_a(inst_dup0)
        self.assertEqual(res_0.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_0.dual_certificate_value, 0.0)

        inst_dup1 = Monotone1in3Instance(2, ((0, 0, 1),))
        res_1 = solve_track_a(inst_dup1)
        self.assertEqual(res_1.status, "SAT")
        self.assertEqual(res_1.assignment, (0, 1))
        self.assertTrue(verify_assignment(inst_dup1, res_1.assignment).is_sat)

    def test_k4_3_unsat_certified(self) -> None:
        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        res = solve_track_a(k4)
        self.assertEqual(res.status, "UNSAT_CERTIFIED")
        self.assertGreater(res.dual_certificate_value, 0.0)
        self.assertEqual(res.bit_summary["overflow_count"], 0)
        self.assertEqual(res.bit_summary["nan_count"], 0)

    def test_shared2_equivalence_and_self_conflict_gadget(self) -> None:
        # (0,1,2) and (0,1,3) => x2 = x3.
        # (2,3,4) forces x2 = x3 = 0 and x4 = 1.
        inst = Monotone1in3Instance(5, ((0, 1, 2), (0, 1, 3), (2, 3, 4)))
        res = solve_track_a(inst)
        self.assertEqual(res.status, "SAT")
        assert res.assignment is not None
        self.assertTrue(verify_assignment(inst, res.assignment).is_sat)
        self.assertEqual(res.assignment[2], 0)
        self.assertEqual(res.assignment[3], 0)
        self.assertEqual(res.assignment[4], 1)

        # Adding (4, 5, 6), (4, 5, 7), (6, 7, 4) -> x4=1 forces x6=x7=0, still SAT
        # Instead add (2, 3, 5) and (4, 5, 0) -> x4=1, x5=1 conflict in (4,5,0) => UNSAT
        inst_unsat = Monotone1in3Instance(
            6,
            ((0, 1, 2), (0, 1, 3), (2, 3, 4), (2, 3, 5), (4, 5, 0)),
        )
        res_u = solve_track_a(inst_unsat)
        self.assertEqual(res_u.status, "UNSAT_CERTIFIED")
        self.assertGreater(res_u.dual_certificate_value, 0.0)

    def test_degree2_3_rlt_implication_gadget(self) -> None:
        # (0, 1, 2) and (0, 3, 4) and (1, 3, 5):
        # Variable 3 conflicts with 0 (from clause 1) and 1 (from clause 2) -> x_3 <= x_2!
        # Add (2, 3, 6): now (2, 3) conflict, so x_3 = x_2*x_3 = 0!
        inst = Monotone1in3Instance(
            7,
            ((0, 1, 2), (0, 3, 4), (1, 3, 5), (2, 3, 6)),
        )
        res = solve_track_a(inst)
        self.assertEqual(res.status, "SAT")
        assert res.assignment is not None
        self.assertTrue(verify_assignment(inst, res.assignment).is_sat)
        self.assertEqual(res.assignment[3], 0)

    def test_disconnected_and_padded_unsat_gadgets(self) -> None:
        deg0_k43 = Monotone1in3Instance(6, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        disconn = Monotone1in3Instance(7, ((0, 1, 2), (3, 4, 5), (3, 4, 6), (3, 5, 6), (4, 5, 6)))
        f2 = generate_planted_f2(15, 9, seed=20261124 + 7).instance
        f2_k43 = Monotone1in3Instance(
            19, f2.clauses + ((15, 16, 17), (15, 16, 18), (15, 17, 18), (16, 17, 18))
        )
        dup_chain = Monotone1in3Instance(3, ((0, 0, 1), (1, 1, 2)))

        for name, inst in (
            ("deg0_k43", deg0_k43),
            ("disconn", disconn),
            ("f2_k43", f2_k43),
            ("dup_chain", dup_chain),
        ):
            res = solve_track_a(inst)
            self.assertEqual(res.status, "UNSAT_CERTIFIED", msg=f"{name} failed UNSAT cert")
            self.assertGreater(res.dual_certificate_value, 0.0)

    def test_planted_f2_sat_and_bitwidth_bounds(self) -> None:
        case = generate_planted_f2(15, 9, seed=20261124 + 7)
        res = solve_track_a(case.instance, SolverConfig(max_iters=300))
        self.assertEqual(res.status, "SAT")
        assert res.assignment is not None
        self.assertTrue(verify_assignment(case.instance, res.assignment).is_sat)
        bs = res.bit_summary
        self.assertEqual(bs["overflow_count"], 0)
        self.assertEqual(bs["nan_count"], 0)
        self.assertGreater(bs["total_ops"], 0)
        self.assertLessEqual(bs["max_int_bit_length"], 40)

    def test_bitwidth_guardrail_overflow(self) -> None:
        # Tight integer bit limit should trip cleanly to OVERFLOW
        case = generate_planted_f2(15, 9, seed=20261124 + 7)
        res = solve_track_a(case.instance, SolverConfig(max_int_bits_limit=2))
        self.assertEqual(res.status, "OVERFLOW")
        self.assertTrue(res.bit_summary["guardrail_tripped"])

    def test_exact_int_farkas_and_ldlt_spectral_dual_on_k4_3(self) -> None:
        from monotone_1in3.bitwidth import BitLedger
        from monotone_1in3.instance import build_incidence
        from monotone_1in3.tracks.track_a_sos_rlt import (
            _exact_int_farkas_check,
            _run_ldlt_spectral_dual,
        )

        k4 = Monotone1in3Instance(4, ((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)))
        ledger = BitLedger()
        # Verify exact integer Farkas check on K4^3 with 4-clique {0,1,2,3}
        cert = _exact_int_farkas_check(
            k=4,
            eq_clauses=((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)),
            cliques=((0, 1, 2, 3),),
            implications=(),
            y=(-1.0 / 3.0, -1.0 / 3.0, -1.0 / 3.0, -1.0 / 3.0),
            mu=(1.0,),
            nu=(),
            ledger=ledger,
        )
        self.assertIsNotNone(cert)
        assert cert is not None
        self.assertGreater(cert, 0.3)

        # Verify square-root-free LDL^T spectral dual certifies K4^3
        inc = build_incidence(k4)
        unsat, d_spec, _ = _run_ldlt_spectral_dual(inc, ledger, SolverConfig(), max_steps=30)
        self.assertTrue(unsat)
        self.assertGreater(d_spec, 0.0)
        self.assertEqual(ledger.overflow_count, 0)
        self.assertEqual(ledger.nan_count, 0)


if __name__ == "__main__":
    unittest.main()
