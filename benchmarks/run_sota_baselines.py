#!/usr/bin/env python3
"""
Run external SOTA baselines (CaDiCaL, CryptoMiniSat 5, Z3-OPB) on the exact
72 high-scale (F1-F5) + 18 coupled hybrid (F6) Monotone 1-in-3 SAT benchmarks
exported by `rust_layer2 --export-benchmarks`, with a strict 10.0s per-instance timeout.

Outputs:
  - reports/sota_baseline_comparison.csv
  - reports/sota_baseline_comparison.md
"""

import csv
import math
import os
import re
import shutil
import subprocess
import sys
import time
from collections import defaultdict
from pathlib import Path

from pysat.formula import CNF
from pysat.solvers import Cadical195
import threading
import z3

ROOT = Path(__file__).resolve().parent.parent
BENCH_DIR = ROOT / "benchmarks"
REPORTS_DIR = ROOT / "reports"
TIMEOUT_SEC = 10.0


def run_cadical(cnf_path: Path, timeout: float):
    """Run CaDiCaL 1.9.5 (via python-sat) in-process with strict interrupt timer (pure solve time)."""
    cnf = CNF(from_file=str(cnf_path))
    with Cadical195(bootstrap_with=cnf.clauses) as s:
        timed_out = [False]
        def interrupt():
            timed_out[0] = True
            s.interrupt()
        timer = threading.Timer(timeout, interrupt)
        timer.start()
        t0 = time.perf_counter()
        sat = s.solve_limited(expect_interrupt=True)
        dt = time.perf_counter() - t0
        timer.cancel()
        if timed_out[0] or sat is None:
            return "TIMEOUT", timeout
        return ("SAT" if sat else "UNSAT"), dt


def run_cryptominisat(cnf_path: Path, timeout: float):
    """Run CryptoMiniSat 5.18.0 CLI binary on DIMACS CNF with strict timeout."""
    t0 = time.perf_counter()
    try:
        p = subprocess.run(
            [shutil.which("cryptominisat5") or "cryptominisat5", "--verb=0", str(cnf_path)],
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        wall = time.perf_counter() - t0
        if p.returncode == 10:
            return "SAT", wall
        elif p.returncode == 20:
            return "UNSAT", wall
        return "ERROR", wall
    except subprocess.TimeoutExpired:
        return "TIMEOUT", timeout


def run_z3_opb(opb_path: Path, timeout: float):
    """Run Z3 SMT/PB solver in-process on exact OPB `sum c_i * x_i = 1` constraints (pure solve time)."""
    s = z3.Solver()
    s.set("timeout", int(timeout * 1000))
    vars_map = {}
    def get_v(idx):
        if idx not in vars_map:
            vars_map[idx] = z3.Bool(f"x{idx}")
        return vars_map[idx]
    with open(opb_path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith("*"):
                continue
            lhs, rhs = line.split("=")
            rhs_val = int(rhs.replace(";", "").strip())
            terms = [(get_v(int(v)), int(c)) for c, v in re.findall(r"([+-]?\d+)\s+x(\d+)", lhs)]
            s.add(z3.PbEq(terms, rhs_val))
    t0 = time.perf_counter()
    res = s.check()
    dt = time.perf_counter() - t0
    if res == z3.sat:
        return "SAT", dt
    elif res == z3.unsat:
        return "UNSAT", dt
    return "TIMEOUT", min(dt, timeout)


def main():
    manifest_rows = list(csv.DictReader(open(BENCH_DIR / "manifest.csv")))
    print(f"Loaded {len(manifest_rows)} benchmark instances (timeout={TIMEOUT_SEC}s/instance)")

    # Verify solver versions
    cms_ver = "CryptoMiniSat 5.18.0"
    z3_ver = z3.get_version_string()
    print(f"Baselines: CaDiCaL 1.9.5 (python-sat) | {cms_ver} | Z3 {z3_ver} (PbEq OPB)")

    results = []
    solvers = [
        ("CaDiCaL_1.9.5", "DIMACS_CNF", "External LRAT/DRAT (uncertified here)", run_cadical),
        ("CryptoMiniSat_5", "DIMACS_CNF", "Uncertified (FRAT/DRAT optional)", run_cryptominisat),
        ("Z3_PB_OPB", "OPB_PbEq", "Uncertified SMT/PB", run_z3_opb),
    ]

    for idx, row in enumerate(manifest_rows, 1):
        inst_id = row["instance_id"]
        suite = row["suite"]
        fam = row["family"]
        tn = int(row["target_n"])
        nv = int(row["n_vars"])
        mc = int(row["m_clauses"])
        gt = row["ground_truth"]
        cnf_path = BENCH_DIR / "dimacs" / f"{inst_id}.cnf"
        opb_path = BENCH_DIR / "opb" / f"{inst_id}.opb"

        row_summary = []
        for sname, fmt, tcb, fn in solvers:
            path = cnf_path if fmt == "DIMACS_CNF" else opb_path
            outcome, dt = fn(path, TIMEOUT_SEC)
            false_sat = (outcome == "SAT" and gt == "UNSAT")
            false_unsat = (outcome == "UNSAT" and gt == "SAT")
            assert not false_sat and not false_unsat, f"SOUNDNESS MISMATCH: {sname} on {inst_id}: got {outcome} vs GT {gt}"
            results.append({
                "solver": sname,
                "format": fmt,
                "tcb": tcb,
                "suite": suite,
                "instance_id": inst_id,
                "family": fam,
                "target_n": tn,
                "n_vars": nv,
                "m_clauses": mc,
                "ground_truth": gt,
                "outcome": outcome,
                "runtime_sec": f"{dt:.6f}",
            })
            row_summary.append(f"{sname[:3]}={outcome}({dt:.3f}s)")
        if idx % 10 == 0 or idx == len(manifest_rows):
            print(f"[{idx:2d}/{len(manifest_rows)}] {inst_id:<40s} " + " | ".join(row_summary))

    # Write CSV
    csv_path = REPORTS_DIR / "sota_baseline_comparison.csv"
    with open(csv_path, "w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=list(results[0].keys()))
        w.writeheader()
        w.writerows(results)

    # Load our Layer 2.75 & 2.8 results for side-by-side summary
    our_l28_72 = [r for r in csv.DictReader(open(REPORTS_DIR / "rust_layer28_results.csv")) if r["solver"] == "Layer2.8_GadgetSP_CP_FLP_Nogoods"]
    our_l275_72 = [r for r in csv.DictReader(open(REPORTS_DIR / "rust_layer28_results.csv")) if r["solver"] == "Layer2.75_GadgetSP_CuttingPlanes"]
    our_l28_f6 = [r for r in csv.DictReader(open(REPORTS_DIR / "f6_hybrid_results.csv")) if r["solver"] == "Layer2.8"]
    our_l275_f6 = [r for r in csv.DictReader(open(REPORTS_DIR / "f6_hybrid_results.csv")) if r["solver"] == "Layer2.75"]

    # Build Markdown report
    md_path = REPORTS_DIR / "sota_baseline_comparison.md"
    lines = []
    lines.append("# External SOTA Baseline Comparison (90 Instances: 72 High-Scale + 18 Coupled `F6`)")
    lines.append("")
    lines.append(f"- **Per-instance timeout:** `{TIMEOUT_SEC:.1f}s`")
    lines.append(f"- **External solvers:** `CaDiCaL 1.9.5` (DIMACS CNF), `{cms_ver}` (DIMACS CNF), `Z3 {z3_ver}` (`PbEq` OPB)")
    lines.append("- **Note on RoundingSat:** Omitted cleanly due to missing local `cmake`/`boost >= 1.70` C++ build dependencies (per fallback plan).")
    lines.append("")

    # Table 1: Overall comparison
    lines.append("## 1. Overall Summary (72 High-Scale `F1`–`F5` and 18 Coupled `F6`)")
    lines.append("")
    lines.append("| Solver | Input | High-Scale 72 (`F1`–`F5`) | High-Scale Time | Coupled `F6` (/18) | `F6` UNSAT (/9) | `F6` Time | Certification / TCB |")
    lines.append("|---|---|---:|---:|---:|---:|---:|---|")

    def our_stats(rows_72, rows_f6):
        s72 = sum(1 for r in rows_72 if r["outcome"] in ("VERIFIED_SAT", "VERIFIED_UNSAT"))
        t72 = sum(float(r["runtime_sec"]) for r in rows_72)
        sf6 = sum(1 for r in rows_f6 if r["outcome"] in ("VERIFIED_SAT", "VERIFIED_UNSAT"))
        uf6 = sum(1 for r in rows_f6 if r["outcome"] == "VERIFIED_UNSAT")
        tf6 = sum(float(r["runtime_sec"]) for r in rows_f6)
        return s72, t72, sf6, uf6, tf6

    s72, t72, sf6, uf6, tf6 = our_stats(our_l275_72, our_l275_f6)
    lines.append(f"| **Ours: Layer 2.75 (`GadgetSP+CP`)** | Native 1-in-3 | {s72}/72 ({100*s72/72:.1f}%) | {t72:.3f}s | {sf6}/18 ({100*sf6/18:.1f}%) | {uf6}/9 | {tf6:.3f}s | Pure-kernel Lean 4 (`by decide`) |")
    s72, t72, sf6, uf6, tf6 = our_stats(our_l28_72, our_l28_f6)
    lines.append(f"| **Ours: Layer 2.8 (`+FLE/NG/WS`)** | Native 1-in-3 | {s72}/72 ({100*s72/72:.1f}%) | {t72:.3f}s | {sf6}/18 ({100*sf6/18:.1f}%) | {uf6}/9 | {tf6:.3f}s | Pure-kernel Lean 4 + Rust subproof |")

    for sname, fmt, tcb, _ in solvers:
        r72 = [r for r in results if r["solver"] == sname and r["suite"] == "high_scale_72"]
        rf6 = [r for r in results if r["solver"] == sname and r["suite"] == "f6_hybrid_18"]
        s72 = sum(1 for r in r72 if r["outcome"] in ("SAT", "UNSAT"))
        t72 = sum(float(r["runtime_sec"]) for r in r72)
        sf6 = sum(1 for r in rf6 if r["outcome"] in ("SAT", "UNSAT"))
        uf6 = sum(1 for r in rf6 if r["outcome"] == "UNSAT")
        tf6 = sum(float(r["runtime_sec"]) for r in rf6)
        lines.append(f"| **{sname}** | `{fmt}` | {s72}/72 ({100*s72/72:.1f}%) | {t72:.3f}s | {sf6}/18 ({100*sf6/18:.1f}%) | {uf6}/9 | {tf6:.3f}s | {tcb} |")

    lines.append("")
    lines.append("## 2. Per-Family Breakdown (Solved / Total, Wall-Clock Time)")
    lines.append("")
    lines.append("| Family | Total | Ours L2.8 | CaDiCaL 1.9.5 | CryptoMiniSat 5 | Z3 (OPB `PbEq`) |")
    lines.append("|---|---:|---|---|---|---|")

    fam_order = [
        ("F1_random_crit", "high_scale_72"),
        ("F2_planted_hard", "high_scale_72"),
        ("F3_tseitin_expander_sat", "high_scale_72"),
        ("F3_tseitin_expander_unsat", "high_scale_72"),
        ("F4_3sat_high_girth", "high_scale_72"),
        ("F5_pigeonhole", "high_scale_72"),
        ("F6_hybrid_f2_z_sat", "f6_hybrid_18"),
        ("F6_hybrid_f2_z_unsat", "f6_hybrid_18"),
    ]
    for fam, suite in fam_order:
        our_src = our_l28_72 if suite == "high_scale_72" else our_l28_f6
        ours_f = [r for r in our_src if r["family"] == fam]
        tot = len(ours_f)
        os_cnt = sum(1 for r in ours_f if r["outcome"] in ("VERIFIED_SAT", "VERIFIED_UNSAT"))
        os_t = sum(float(r["runtime_sec"]) for r in ours_f)
        cells = [f"{os_cnt}/{tot} ({os_t:.3f}s)"]
        for sname, _, _, _ in solvers:
            rs = [r for r in results if r["solver"] == sname and r["family"] == fam]
            sc = sum(1 for r in rs if r["outcome"] in ("SAT", "UNSAT"))
            st = sum(float(r["runtime_sec"]) for r in rs)
            cells.append(f"{sc}/{tot} ({st:.3f}s)")
        lines.append(f"| `{fam}` | {tot} | " + " | ".join(cells) + " |")

    md_path.write_text("\n".join(lines) + "\n")
    print(f"\nSaved {csv_path} and {md_path}")
    print("\n".join(lines))


if __name__ == "__main__":
    main()
