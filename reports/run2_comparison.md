# Run #2 Comparative Benchmark Report (Parallel Tracks A–D vs Run #1 PD-PFGC)

- **Suite:** 140 instances (`seed=20261124`, $n \in \{15, 30, 60\}$; 101 SAT, 39 UNSAT)
- **Step Budgets:** Deterministic polynomial $T_{\max}(n, m)$ (`max_time_sec=None`, zero wall-clock censoring)
- **AST Isolation Audit:** `CLEAN (0 forbidden solver/harness imports)`

## 1. Overall Side-by-Side Comparison (140 Instances)

| Solver | `VERIFIED_SAT` (/101) | `VERIFIED_UNSAT` (/39) | `UNRESOLVED` | `FALSE_SAT` | `FALSE_UNSAT` | `OVERFLOW` | `max_int_bits` | `max_float_exp` | Runtime (s) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| **Run #1 (PD-PFGC)** | 63 (62.4%) | 9 (23.1%) | 68 | 0 | 0 | 0 | 4 | 55 | 71.38 |
| **Track A (SoS/RLT)** | 101 (100.0%) | 29 (74.4%) | 10 | 0 | 0 | 0 | 6 | 12 | 3.56 |
| **Track B (Symplectic)** | 87 (86.1%) | 11 (28.2%) | 42 | 0 | 0 | 0 | 4 | 6 | 16.71 |
| **Track C (F2+Groebner)** | 101 (100.0%) | 39 (100.0%) | 0 | 0 | 0 | 0 | 3 | 31 | 7.64 |
| **Track D (Decimation)** | 101 (100.0%) | 29 (74.4%) | 10 | 0 | 0 | 0 | 4 | 31 | 21.76 |

## 2. Per-Family Side-by-Side Comparison (`VERIFIED_SAT` / `VERIFIED_UNSAT` / `UNRESOLVED`)

| Family (SAT/UNSAT) | Run #1 (`PD-PFGC`) | Track A (`SoS/RLT`) | Track B (`Symplectic`) | Track C (`F2+Groebner`) | Track D (`Decimation`) |
|---|---|---|---|---|---|
| `F1_random` (41/19) | 24S / 9U / 27? | 41S / 19U / 0? | 36S / 11U / 13? | 41S / 19U / 0? | 41S / 19U / 0? |
| `F2_planted_sat` (30/0) | 21S / 0U / 9? | 30S / 0U / 0? | 25S / 0U / 5? | 30S / 0U / 0? | 30S / 0U / 0? |
| `F3a_tseitin_sat` (15/0) | 12S / 0U / 3? | 15S / 0U / 0? | 14S / 0U / 1? | 15S / 0U / 0? | 15S / 0U / 0? |
| `F3b_tseitin_unsat` (0/15) | 0S / 0U / 15? | 0S / 5U / 10? | 0S / 0U / 15? | 0S / 15U / 0? | 0S / 5U / 10? |
| `F4a_3sat_sat` (15/0) | 6S / 0U / 9? | 15S / 0U / 0? | 12S / 0U / 3? | 15S / 0U / 0? | 15S / 0U / 0? |
| `F4b_3sat_unsat` (0/5) | 0S / 0U / 5? | 0S / 5U / 0? | 0S / 0U / 5? | 0S / 5U / 0? | 0S / 5U / 0? |

## 3. Hardest Regime ($n = 60$) Per-Family Breakdown

| Family @ $n=60$ (SAT/UNSAT) | Run #1 (`PD-PFGC`) | Track A (`SoS/RLT`) | Track B (`Symplectic`) | Track C (`F2+Groebner`) | Track D (`Decimation`) |
|---|---|---|---|---|---|
| `F1_random` (12/8) | 2S / 1U / 17? | 12S / 8U / 0? | 9S / 2U / 9? | 12S / 8U / 0? | 12S / 8U / 0? |
| `F2_planted_sat` (10/0) | 4S / 0U / 6? | 10S / 0U / 0? | 7S / 0U / 3? | 10S / 0U / 0? | 10S / 0U / 0? |
| `F3a_tseitin_sat` (5/0) | 2S / 0U / 3? | 5S / 0U / 0? | 4S / 0U / 1? | 5S / 0U / 0? | 5S / 0U / 0? |
| `F3b_tseitin_unsat` (0/5) | 0S / 0U / 5? | 0S / 0U / 5? | 0S / 0U / 5? | 0S / 5U / 0? | 0S / 0U / 5? |
| `F4a_3sat_sat` (5/0) | 0S / 0U / 5? | 5S / 0U / 0? | 2S / 0U / 3? | 5S / 0U / 0? | 5S / 0U / 0? |
| `F4b_3sat_unsat` (0/5) | 0S / 0U / 5? | 0S / 5U / 0? | 0S / 0U / 5? | 0S / 5U / 0? | 0S / 5U / 0? |

## 4. `t=0` Factorization Bit-Width Fix (`Fraction` Cholesky vs `LDL^T` vs Bareiss)

| Instance | Method | Status | `max_int_bits` | `max_fraction_bits` | Guardrail Tripped |
|---|---|---|---:|---:|---|
| `K4_3_UNSAT` | Run #1 Fraction Cholesky (sqrt) | `OVERFLOW` | 1784 | 3566 | `True` |
| `K4_3_UNSAT` | Run #2 Fraction LDL^T (sqrt-free) | `OK` | 5 | 6 | `False` |
| `K4_3_UNSAT` | Run #2 Bareiss Integer Elimination | `OK` | 11 | 0 | `False` |
| `F2_n15_m9_SAT` | Run #1 Fraction Cholesky (sqrt) | `OVERFLOW` | 1784 | 3566 | `True` |
| `F2_n15_m9_SAT` | Run #2 Fraction LDL^T (sqrt-free) | `OK` | 32 | 59 | `False` |
| `F2_n15_m9_SAT` | Run #2 Bareiss Integer Elimination | `OK` | 32 | 0 | `False` |
