# Layer 2 vs. Layer 2.5 vs. Layer 2.75 Side-by-Side Falsification Report

## 1. Parity Suite Validation (140 Instances, $n \in \{15, 30, 60\}$)
| Solver | `VERIFIED_SAT` (/101) | `VERIFIED_UNSAT` (/39) | `UNRESOLVED` | `FALSE_SAT` | `FALSE_UNSAT` | `OVERFLOW` | Runtime (s) |
|---|---:|---:|---:|---:|---:|---:|---:|
| **Layer 2 (`HybridGroebnerCascade`)** | 101 | 34 | 5 | 0 | 0 | 0 | 0.0341 |
| **Layer 2.5 (`GadgetSPCascade`)** | 101 | 39 | 0 | 0 | 0 | 0 | 0.0108 |
| **Layer 2.75 (`GadgetSP + CuttingPlanes`)** | 101 | 39 | 0 | 0 | 0 | 0 | 0.0160 |

## 2. High-Scale Side-by-Side Comparison ($n \in \{150, 300, 600\}$, 72 Instances)

| Family | Target $n$ | L2 Solve (S/U/?) | L2.5 Solve (S/U/?) | L2.75 Solve (S/U/?) | L2.75 Avg Time (s) | L2.75 `max_int`/`exp` |
|---|---:|---|---|---|---:|---|
| `F1_random_crit` | 150 | 100.0% (5S/1U/0?) | 100.0% (5S/1U/0?) | **100.0%** (5S/1U/0?) | 0.0011 | 2 / 0 |
| `F1_random_crit` | 300 | 83.3% (4S/1U/1?) | 100.0% (5S/1U/0?) | **100.0%** (5S/1U/0?) | 0.0079 | 2 / 0 |
| `F1_random_crit` | 600 | 16.7% (1S/0U/5?) | 83.3% (4S/1U/1?) | **83.3%** (4S/1U/1?) | 0.0481 | 2 / 0 |
| `F2_planted_hard` | 150 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0014 | 3 / -2 |
| `F2_planted_hard` | 300 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0052 | 4 / -2 |
| `F2_planted_hard` | 600 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0193 | 3 / -2 |
| `F3_tseitin_expander_sat` | 150 | 100.0% (3S/0U/0?) | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0014 | 2 / -1 |
| `F3_tseitin_expander_sat` | 300 | 100.0% (3S/0U/0?) | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0037 | 2 / -1 |
| `F3_tseitin_expander_sat` | 600 | 100.0% (3S/0U/0?) | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0121 | 2 / -1 |
| `F3_tseitin_expander_unsat` | 150 | 0.0% (0S/0U/3?) | 100.0% (0S/3U/0?) | **100.0%** (0S/3U/0?) | 0.0002 | 1 / 0 |
| `F3_tseitin_expander_unsat` | 300 | 0.0% (0S/0U/3?) | 100.0% (0S/3U/0?) | **100.0%** (0S/3U/0?) | 0.0005 | 1 / 0 |
| `F3_tseitin_expander_unsat` | 600 | 0.0% (0S/0U/3?) | 100.0% (0S/3U/0?) | **100.0%** (0S/3U/0?) | 0.0012 | 1 / 0 |
| `F4_3sat_high_girth` | 150 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0013 | 2 / -1 |
| `F4_3sat_high_girth` | 300 | 60.0% (3S/0U/2?) | 60.0% (3S/0U/2?) | **60.0%** (3S/0U/2?) | 0.0189 | 2 / -1 |
| `F4_3sat_high_girth` | 600 | 40.0% (2S/0U/3?) | 60.0% (3S/0U/2?) | **60.0%** (3S/0U/2?) | 0.0936 | 2 / -1 |
| `F5_pigeonhole` | 150 | 0.0% (0S/0U/2?) | 0.0% (0S/0U/2?) | **100.0%** (0S/2U/0?) | 0.0007 | 2 / 0 |
| `F5_pigeonhole` | 300 | 0.0% (0S/0U/2?) | 0.0% (0S/0U/2?) | **100.0%** (0S/2U/0?) | 0.0025 | 2 / 0 |
| `F5_pigeonhole` | 600 | 0.0% (0S/0U/2?) | 0.0% (0S/0U/2?) | **100.0%** (0S/2U/0?) | 0.0067 | 2 / 0 |

- **Layer 2 (72 high-scale):** `VERIFIED_SAT=44`, `VERIFIED_UNSAT=2`, `UNRESOLVED=26`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `1.618s`
- **Layer 2.5 (72 high-scale):** `VERIFIED_SAT=49`, `VERIFIED_UNSAT=12`, `UNRESOLVED=11`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `1.795s`
- **Layer 2.75 (72 high-scale):** `VERIFIED_SAT=49`, `VERIFIED_UNSAT=18`, `UNRESOLVED=5`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `1.118s`
