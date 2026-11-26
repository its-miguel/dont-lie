# Reproducibility Guide: Multi-Lens $\mathbb{F}_2 + \mathbb{Z} + \text{Cavity}$ Monotone 1-in-3 SAT Solver & Lean 4 Kernel Bridge

**Repository:** https://github.com/its-miguel/dont-lie

This directory contains our research manuscripts and companion guides:
- `dont_lie_paper.md` / `.tex` / `.pdf` — arXiv / peer-review manuscript (*"Don't Lie: Fast, Zero-Backtracking Constraint Solving with Machine-Checked Proofs in Lean 4"*).
- `monotone_1in3_dual_proof_solver.md` / `.tex` / `.pdf` — Complete technical paper with audited tables, SOTA baselines, TikZ architecture diagram, and Lean 4 pure-kernel bridge.
- `monotone_1in3_undergrad_guide.md` / `.tex` / `.pdf` — Undergraduate & software engineer's ground-up guide (*"Building a Solver That Cannot Lie: From Light-Switch Puzzles to Kernel-Verified Proofs in Lean 4"*) with worked examples, `tcolorbox` intuition callouts, and TikZ diagrams.
- `monotone_1in3_socratic_guide.md` — Four-tier progressive Socratic companion explainer.
- **Interactive Paper Skill (`paper-pillar-explainer`):** Available at `skills/paper-pillar-explainer/SKILL.md`. Ask your AI assistant to use `paper-pillar-explainer` on any manuscript in this directory for an adaptive, pillar-by-pillar interactive walkthrough matched to your background.

---

## 1. Reproducing Layer 1 (Python Prototype & Tests)
From the repository root:
```bash
python3 -m unittest discover -s tests
```
Expected: `71/71` unit tests passing (including bit-width bounds, independent verifier soundness, and Run #1 / Run #2 track audits).

---

## 2. Reproducing Layer 2–2.8 (Pure Rust `std`-Only Benchmarks & Diagnostics)
From `rust_layer2/`:

### 2.1 Unit Tests
```bash
cargo test --release
```
Expected: `5/5` tests passing (`test_k4_3_and_small_php_unsat`, `test_schaefer_3or_truth_table`, `test_tseitin_3xor_truth_table`, `test_gadget_sp_breaks_tseitin_expander_unsat`, `test_cutting_planes_refutes_pigeonhole`).

### 2.2 Full Benchmark Suite (140 Parity + 72 High-Scale Instances)
```bash
cargo run --release
```
Generates:
- `../reports/rust_layer28_results.csv`
- `../reports/rust_layer28_comparison.md`

Expected summary:
- **Parity 140 ($n \in \{15, 30, 60\}$):** Layer 2.5 / 2.75 / 2.8 achieve `140/140 (100.0%)`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`.
- **High-Scale 72 ($n \in \{150, 300, 600\}$):**
  - Layer 2: `46/72` (`63.9%`)
  - Layer 2.5: `61/72` (`84.7%`)
  - Layer 2.75: `67/72` (`93.1%`)
  - Layer 2.8: **`69/72` (`95.8%`)** (`49/49` SAT, `20/23` UNSAT, `48/48` for $n \le 306$, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`).

### 2.3 Isolated Frontier Diagnostic, Coupled `F6` Suite & SOTA Baselines
```bash
cargo run --release -- --diagnose-frontier
cargo run --release -- --frontier-l28
cargo run --release -- --benchmark-f6
cargo run --release -- --export-benchmarks
python3 ../benchmarks/run_sota_baselines.py
```
Generates `../reports/f6_hybrid_results.csv`, `../reports/sota_baseline_comparison.csv`, and `../reports/sota_baseline_comparison.md` comparing Layer 2.75 / 2.8 against CaDiCaL 1.9.5, CryptoMiniSat 5.18.0, and Z3 5.4.1 (`10.0s` timeout/instance).

### 2.4 Exporting High-Scale UNSAT Certificates to Lean 4
```bash
cargo run --release -- --export-cert
cargo run --release -- --export-f6-cert
```
Exports and backward-cone prunes:
- `../lean4_layer3/Monotone1in3Layer3/GeneratedCerts/Tseitin610Cert.lean` (`3,780 -> 626` steps)
- `../lean4_layer3/Monotone1in3Layer3/GeneratedCerts/Pigeonhole637Cert.lean` (`9,936 -> 1,914` steps)
- `../lean4_layer3/Monotone1in3Layer3/GeneratedCerts/HybridF2Z600Cert.lean` (`11,629 -> 1,329` steps)

---

## 3. Reproducing Layer 3 (Lean 4 Pure-Kernel Verification)
Requires Lean `v4.36.0` / Lake `5.0.0` (e.g. via `elan` at `~/.elan/bin/lake`).
From `lean4_layer3/`:
```bash
lake build
```
Expected: `Build completed successfully (22 jobs)` with **0 errors, 0 warnings, 0 `sorry`s**, pure-kernel verifying (`by decide`):
- `Monotone1in3.unified_certificate_sound`
- `Monotone1in3.Bridge.tseitin_610_unsat` ($n = 610$)
- `Monotone1in3.Bridge.php_637_unsat` ($\text{PHP}_9^{10}$, $n = 637$)
- `Monotone1in3.Bridge.hybrid_f2_z_783_unsat` (coupled $\mathbb{F}_2 \oplus \mathbb{Z}$ trap, $n = 783$)

---

## 4. Compiling the LaTeX Papers (Optional)
Using `tectonic` (recommended, auto-fetches minimal TeX packages) or `pdflatex`:
```bash
cd paper
tectonic monotone_1in3_dual_proof_solver.tex
tectonic monotone_1in3_undergrad_guide.tex
```
*(Or with `pdflatex`: run `pdflatex <file>.tex` twice to resolve cross-references.)*
