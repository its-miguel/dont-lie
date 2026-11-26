"""Run #2 Comparative Benchmark Runner for Parallel Tracks A, B, C, D vs Run #1 PD-PFGC.

Evaluates all 4 tracks on the exact same 140-instance suite (seed=20261124)
with deterministic polynomial step budgets (no wall-clock censoring), verifies
every outcome with the independent verifier, audits AST isolation (zero fallback
solvers), and emits reports/run2_comparison.md and reports/run2_comparison.json.
"""

from __future__ import annotations

import ast
from collections import defaultdict
import json
from pathlib import Path
import time
from typing import Any, Callable

from .bitwidth import BitLedger, TrackedInt, make_scalar
from .generators import BenchmarkCase, generate_benchmark_suite, generate_planted_f2
from .harness import classify_outcome
from .instance import Monotone1in3Instance, build_incidence
from .primitives import (
    SparseOperators,
    bareiss_spd_factor_int,
    build_M0,
    cholesky_factor,
    ldlt_factor,
)
from .solver import SolverConfig, SolverResult
from .tracks.track_a_sos_rlt import solve_track_a
from .tracks.track_b_symplectic import solve_track_b
from .tracks.track_c_f2_groebner import solve_track_c
from .tracks.track_d_decimation import solve_track_d

FORBIDDEN_IMPORTS = {
    "z3",
    "pysat",
    "scipy",
    "pulp",
    "ortools",
    "cvxpy",
    "sympy",
    "networkx",
    "generators",
    "harness",
}

FAMILIES = [
    "F1_random",
    "F2_planted_sat",
    "F3a_tseitin_sat",
    "F3b_tseitin_unsat",
    "F4a_3sat_sat",
    "F4b_3sat_unsat",
]


def audit_track_ast(track_files: list[Path]) -> list[dict[str, Any]]:
    """Verify zero forbidden solver/harness imports across all track modules."""
    findings: list[dict[str, Any]] = []
    for path in track_files:
        tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        imports: list[str] = []
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for alias in node.names:
                    top = alias.name.split(".")[0]
                    imports.append(top)
                    if top in FORBIDDEN_IMPORTS:
                        findings.append({"file": path.name, "forbidden_import": alias.name})
            elif isinstance(node, ast.ImportFrom):
                mod = (node.module or "").split(".")[-1]
                top = (node.module or "").split(".")[0]
                if mod in FORBIDDEN_IMPORTS or top in FORBIDDEN_IMPORTS:
                    findings.append({"file": path.name, "forbidden_import": node.module})
    return findings


def run_t0_factorization_probe() -> list[dict[str, Any]]:
    """Compare t=0 M_0 factorization bit-width: naive Fraction Cholesky vs LDL^T vs Bareiss."""
    k4 = Monotone1in3Instance(
        n_vars=4,
        clauses=((0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)),
        metadata={"name": "K4_3_UNSAT"},
    )
    f2_case = generate_planted_f2(15, 9, seed=20261124 + 99)
    probes = [
        ("K4_3_UNSAT", k4),
        ("F2_n15_m9_SAT", f2_case.instance),
    ]
    rows: list[dict[str, Any]] = []
    for name, inst in probes:
        inc = build_incidence(inst)

        # 1. Run #1 Naive Fraction Cholesky (limit 2048)
        ledger_chol = BitLedger(max_fraction_bits_limit=2048, raise_on_guardrail=True)
        ops_chol = SparseOperators(inc, ledger_chol, mode="fraction")
        m0_chol = build_M0(ops_chol, ops_chol.one)
        chol_status = "OK"
        try:
            fac = cholesky_factor(m0_chol, ledger_chol, mode="fraction")
            if fac is None:
                chol_status = "FAILED"
        except Exception:
            chol_status = "OVERFLOW"
        s_chol = ledger_chol.summary()
        rows.append({
            "instance": name,
            "method": "Run #1 Fraction Cholesky (sqrt)",
            "status": chol_status,
            "max_int_bits": s_chol["max_int_bit_length"],
            "max_fraction_bits": s_chol["max_fraction_bits"],
            "guardrail_tripped": s_chol["guardrail_tripped"],
        })

        # 2. Run #2 Square-root-free Fraction LDL^T (build M0 = I + A^T A directly without t_sqrt)
        ledger_ldlt = BitLedger(max_fraction_bits_limit=2048, raise_on_guardrail=True)
        n_p = inst.n_vars
        zero_f = make_scalar(0, ledger_ldlt, mode="fraction")
        one_f = make_scalar(1, ledger_ldlt, mode="fraction")
        m0_ldlt = [[one_f if i == j else zero_f for j in range(n_p)] for i in range(n_p)]
        for terms in inc.clause_terms:
            for i, ci in terms:
                ci_s = make_scalar(ci, ledger_ldlt, mode="fraction")
                for j, cj in terms:
                    cj_s = make_scalar(cj, ledger_ldlt, mode="fraction")
                    m0_ldlt[i][j] = m0_ldlt[i][j] + ci_s * cj_s
        ldlt_status = "OK"
        try:
            fac_l = ldlt_factor(m0_ldlt, ledger_ldlt, mode="fraction")
            if fac_l is None:
                ldlt_status = "FAILED"
        except Exception:
            ldlt_status = "OVERFLOW"
        s_ldlt = ledger_ldlt.summary()
        rows.append({
            "instance": name,
            "method": "Run #2 Fraction LDL^T (sqrt-free)",
            "status": ldlt_status,
            "max_int_bits": s_ldlt["max_int_bit_length"],
            "max_fraction_bits": s_ldlt["max_fraction_bits"],
            "guardrail_tripped": s_ldlt["guardrail_tripped"],
        })

        # 3. Run #2 Fraction-free Bareiss integer elimination
        ledger_bar = BitLedger(max_int_bits_limit=2048, raise_on_guardrail=True)
        ops_bar = SparseOperators(inc, ledger_bar, mode="float64")
        one_ti = TrackedInt(1, ledger_bar, count_op=False)
        m0_int = [
            [
                (ops_bar.ata_int[i][j] + one_ti) if i == j else ops_bar.ata_int[i][j]
                for j in range(inst.n_vars)
            ]
            for i in range(inst.n_vars)
        ]
        bar_status = "OK"
        try:
            bf = bareiss_spd_factor_int(m0_int, ledger_bar)
            if bf is None:
                bar_status = "FAILED"
        except Exception:
            bar_status = "OVERFLOW"
        s_bar = ledger_bar.summary()
        rows.append({
            "instance": name,
            "method": "Run #2 Bareiss Integer Elimination",
            "status": bar_status,
            "max_int_bits": s_bar["max_int_bit_length"],
            "max_fraction_bits": s_bar["max_fraction_bits"],
            "guardrail_tripped": s_bar["guardrail_tripped"],
        })
    return rows


def _summarize_records(records: list[dict[str, Any]], total_runtime: float) -> dict[str, Any]:
    """Aggregate per-family, per-(family,n), and overall metrics."""
    overall = {
        "VERIFIED_SAT": 0,
        "VERIFIED_UNSAT": 0,
        "UNRESOLVED": 0,
        "OVERFLOW": 0,
        "FALSE_SAT_CLAIM": 0,
        "FALSE_UNSAT_CLAIM": 0,
        "max_int_bits": 0,
        "max_float_exp": None,
        "runtime_sec": round(total_runtime, 3),
    }
    by_family: dict[str, dict[str, Any]] = {}
    by_family_n: dict[str, dict[str, Any]] = {}

    for rec in records:
        out = rec["outcome"]
        overall[out] += 1
        ib = rec["max_int_bits"]
        fe = rec["max_float_exp"]
        if ib > overall["max_int_bits"]:
            overall["max_int_bits"] = ib
        if fe is not None and (overall["max_float_exp"] is None or fe > overall["max_float_exp"]):
            overall["max_float_exp"] = fe

        fam = rec["family"]
        for bucket_map, key in ((by_family, fam), (by_family_n, f"{fam}|n={rec['n']}")):
            b = bucket_map.setdefault(
                key,
                {
                    "total": 0,
                    "gt_sat": 0,
                    "gt_unsat": 0,
                    "VERIFIED_SAT": 0,
                    "VERIFIED_UNSAT": 0,
                    "UNRESOLVED": 0,
                    "OVERFLOW": 0,
                    "FALSE_SAT_CLAIM": 0,
                    "FALSE_UNSAT_CLAIM": 0,
                    "max_int_bits": 0,
                    "max_float_exp": None,
                },
            )
            b["total"] += 1
            if rec["ground_truth"] == "SAT":
                b["gt_sat"] += 1
            else:
                b["gt_unsat"] += 1
            b[out] += 1
            if ib > b["max_int_bits"]:
                b["max_int_bits"] = ib
            if fe is not None and (b["max_float_exp"] is None or fe > b["max_float_exp"]):
                b["max_float_exp"] = fe

    return {
        "overall": overall,
        "by_family": by_family,
        "by_family_n": by_family_n,
    }


def load_run1_baseline(results_json_path: Path) -> dict[str, Any]:
    """Load Run #1 PD-PFGC baseline summary from reports/results.json."""
    data = json.loads(results_json_path.read_text(encoding="utf-8"))
    records: list[dict[str, Any]] = []
    for r in data["runs"]:
        records.append({
            "instance_id": r["instance_id"],
            "family": r["family"],
            "n": r["n"],
            "ground_truth": r["ground_truth"],
            "outcome": r["outcome"],
            "max_int_bits": r["max_int_bit_width"],
            "max_float_exp": r["max_float_exp"],
        })
    return _summarize_records(
        records,
        float(data.get("metadata", {}).get("total_runtime_sec", 0.0)),
    )


def evaluate_track(
    name: str,
    solver_fn: Callable[[Monotone1in3Instance, SolverConfig | None], SolverResult],
    cases: list[BenchmarkCase],
) -> dict[str, Any]:
    """Run one track across all 140 benchmark cases with deterministic polynomial step budgets."""
    t0 = time.perf_counter()
    records: list[dict[str, Any]] = []
    for case in cases:
        cfg = SolverConfig(
            max_iters=None,       # use track's deterministic polynomial T_max(n, m)
            max_time_sec=None,    # NO wall-clock censoring
            mode="float64",
            record_iter_history=False,
        )
        res = solver_fn(case.instance, cfg)
        outcome, viol = classify_outcome(case, res)
        bs = res.bit_summary
        records.append({
            "instance_id": case.instance_id,
            "family": case.family,
            "n": case.n_vars,
            "m": case.m_clauses,
            "ground_truth": case.ground_truth,
            "status": res.status,
            "outcome": outcome,
            "termination_reason": res.termination_reason,
            "iterations": res.iterations,
            "runtime_sec": round(res.runtime_sec, 6),
            "clause_violation_count": viol,
            "max_int_bits": int(bs.get("max_int_bit_length", 0)),
            "max_float_exp": bs.get("max_float_exp"),
            "max_dynamic_range_bits": int(bs.get("max_dynamic_range_bits", 0)),
        })
    elapsed = time.perf_counter() - t0
    summary = _summarize_records(records, elapsed)
    summary["name"] = name
    summary["runs"] = records
    return summary


def run_comparison(project_root: Path) -> dict[str, Any]:
    """Execute full Run #2 comparative benchmark and write Markdown + JSON reports."""
    reports_dir = project_root / "reports"
    tracks_dir = project_root / "src" / "monotone_1in3" / "tracks"
    track_files = sorted(p for p in tracks_dir.glob("track_*.py"))
    ast_findings = audit_track_ast(track_files)
    if ast_findings:
        raise RuntimeError(f"AST isolation audit failed: {ast_findings}")

    cases = generate_benchmark_suite(seed=20261124, fast=False)
    baseline = load_run1_baseline(reports_dir / "results.json")
    baseline["name"] = "Run #1 (PD-PFGC)"

    tracks: list[tuple[str, Callable[[Monotone1in3Instance, SolverConfig | None], SolverResult]]] = [
        ("Track A (SoS/RLT)", solve_track_a),
        ("Track B (Symplectic)", solve_track_b),
        ("Track C (F2+Groebner)", solve_track_c),
        ("Track D (Decimation)", solve_track_d),
    ]
    results: dict[str, Any] = {"Run #1 (PD-PFGC)": baseline}
    for name, fn in tracks:
        results[name] = evaluate_track(name, fn, cases)

    t0_probe = run_t0_factorization_probe()

    payload = {
        "seed": 20261124,
        "total_instances": len(cases),
        "ast_audit_clean": len(ast_findings) == 0,
        "t0_factorization_probe": t0_probe,
        "solvers": {
            k: {
                "overall": v["overall"],
                "by_family": v["by_family"],
                "by_family_n": v["by_family_n"],
            }
            for k, v in results.items()
        },
    }
    (reports_dir / "run2_comparison.json").write_text(
        json.dumps(payload, indent=2), encoding="utf-8"
    )

    md = _render_markdown_report(payload)
    (reports_dir / "run2_comparison.md").write_text(md, encoding="utf-8")
    return payload


def _render_markdown_report(payload: dict[str, Any]) -> str:
    solvers = payload["solvers"]
    order = [
        "Run #1 (PD-PFGC)",
        "Track A (SoS/RLT)",
        "Track B (Symplectic)",
        "Track C (F2+Groebner)",
        "Track D (Decimation)",
    ]
    lines: list[str] = [
        "# Run #2 Comparative Benchmark Report (Parallel Tracks A–D vs Run #1 PD-PFGC)",
        "",
        f"- **Suite:** 140 instances (`seed={payload['seed']}`, $n \\in \\{{15, 30, 60\\}}$; 101 SAT, 39 UNSAT)",
        "- **Step Budgets:** Deterministic polynomial $T_{\\max}(n, m)$ (`max_time_sec=None`, zero wall-clock censoring)",
        f"- **AST Isolation Audit:** `{'CLEAN (0 forbidden solver/harness imports)' if payload['ast_audit_clean'] else 'FAILED'}`",
        "",
        "## 1. Overall Side-by-Side Comparison (140 Instances)",
        "",
        "| Solver | `VERIFIED_SAT` (/101) | `VERIFIED_UNSAT` (/39) | `UNRESOLVED` | `FALSE_SAT` | `FALSE_UNSAT` | `OVERFLOW` | `max_int_bits` | `max_float_exp` | Runtime (s) |",
        "|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|",
    ]
    for s in order:
        ov = solvers[s]["overall"]
        lines.append(
            f"| **{s}** | {ov['VERIFIED_SAT']} ({100.0*ov['VERIFIED_SAT']/101:.1f}%) | "
            f"{ov['VERIFIED_UNSAT']} ({100.0*ov['VERIFIED_UNSAT']/39:.1f}%) | "
            f"{ov['UNRESOLVED']} | {ov['FALSE_SAT_CLAIM']} | {ov['FALSE_UNSAT_CLAIM']} | "
            f"{ov['OVERFLOW']} | {ov['max_int_bits']} | {ov['max_float_exp']} | {ov['runtime_sec']:.2f} |"
        )

    lines.extend([
        "",
        "## 2. Per-Family Side-by-Side Comparison (`VERIFIED_SAT` / `VERIFIED_UNSAT` / `UNRESOLVED`)",
        "",
        "| Family (SAT/UNSAT) | Run #1 (`PD-PFGC`) | Track A (`SoS/RLT`) | Track B (`Symplectic`) | Track C (`F2+Groebner`) | Track D (`Decimation`) |",
        "|---|---|---|---|---|---|",
    ])
    for fam in FAMILIES:
        b0 = solvers[order[0]]["by_family"][fam]
        row = [f"`{fam}` ({b0['gt_sat']}/{b0['gt_unsat']})"]
        for s in order:
            b = solvers[s]["by_family"][fam]
            row.append(f"{b['VERIFIED_SAT']}S / {b['VERIFIED_UNSAT']}U / {b['UNRESOLVED']}?")
        lines.append("| " + " | ".join(row) + " |")

    lines.extend([
        "",
        "## 3. Hardest Regime ($n = 60$) Per-Family Breakdown",
        "",
        "| Family @ $n=60$ (SAT/UNSAT) | Run #1 (`PD-PFGC`) | Track A (`SoS/RLT`) | Track B (`Symplectic`) | Track C (`F2+Groebner`) | Track D (`Decimation`) |",
        "|---|---|---|---|---|---|",
    ])
    for fam in FAMILIES:
        key = f"{fam}|n=60"
        if key not in solvers[order[0]]["by_family_n"]:
            continue
        b0 = solvers[order[0]]["by_family_n"][key]
        row = [f"`{fam}` ({b0['gt_sat']}/{b0['gt_unsat']})"]
        for s in order:
            b = solvers[s]["by_family_n"][key]
            row.append(f"{b['VERIFIED_SAT']}S / {b['VERIFIED_UNSAT']}U / {b['UNRESOLVED']}?")
        lines.append("| " + " | ".join(row) + " |")

    lines.extend([
        "",
        "## 4. `t=0` Factorization Bit-Width Fix (`Fraction` Cholesky vs `LDL^T` vs Bareiss)",
        "",
        "| Instance | Method | Status | `max_int_bits` | `max_fraction_bits` | Guardrail Tripped |",
        "|---|---|---|---:|---:|---|",
    ])
    for r in payload["t0_factorization_probe"]:
        lines.append(
            f"| `{r['instance']}` | {r['method']} | `{r['status']}` | "
            f"{r['max_int_bits']} | {r['max_fraction_bits']} | `{r['guardrail_tripped']}` |"
        )

    lines.append("")
    return "\n".join(lines)


if __name__ == "__main__":
    root = Path(__file__).resolve().parents[2]
    res = run_comparison(root)
    print(json.dumps({k: v["overall"] for k, v in res["solvers"].items()}, indent=2))
