# Layer 2 vs. Layer 2.5 vs. Layer 2.75 vs. Layer 2.8 Side-by-Side Falsification Report

## 1. Parity Suite Validation (140 Instances, $n \in \{15, 30, 60\}$)
| Solver | `VERIFIED_SAT` (/101) | `VERIFIED_UNSAT` (/39) | `UNRESOLVED` | `FALSE_SAT` | `FALSE_UNSAT` | `OVERFLOW` | Runtime (s) |
|---|---:|---:|---:|---:|---:|---:|---:|
| **Layer 2 (`HybridGroebnerCascade`)** | 101 | 34 | 5 | 0 | 0 | 0 | 0.0335 |
| **Layer 2.5 (`GadgetSPCascade`)** | 101 | 39 | 0 | 0 | 0 | 0 | 0.0114 |
| **Layer 2.75 (`GadgetSP + CuttingPlanes`)** | 101 | 39 | 0 | 0 | 0 | 0 | 0.0158 |
| **Layer 2.8 (`GadgetSP + CP + FLP + Nogoods`)** | 101 | 39 | 0 | 0 | 0 | 0 | 0.0720 |

## 2. High-Scale Side-by-Side Comparison ($n \in \{150, 300, 600\}$, 72 Instances)

| Family | Target $n$ | L2.5 Solve (S/U/?) | L2.75 Solve (S/U/?) | L2.8 Solve (S/U/?) | L2.8 Avg Time (s) | L2.8 `max_int`/`exp` |
|---|---:|---|---|---|---:|---|
| `F1_random_crit` | 150 | 100.0% (5S/1U/0?) | 100.0% (5S/1U/0?) | **100.0%** (5S/1U/0?) | 0.0115 | 2 / 0 |
| `F1_random_crit` | 300 | 100.0% (5S/1U/0?) | 100.0% (5S/1U/0?) | **100.0%** (5S/1U/0?) | 0.0487 | 2 / 0 |
| `F1_random_crit` | 600 | 83.3% (4S/1U/1?) | 83.3% (4S/1U/1?) | **83.3%** (4S/1U/1?) | 0.1861 | 2 / 0 |
| `F2_planted_hard` | 150 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0079 | 3 / -2 |
| `F2_planted_hard` | 300 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0344 | 4 / -2 |
| `F2_planted_hard` | 600 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.1613 | 3 / -2 |
| `F3_tseitin_expander_sat` | 150 | 100.0% (3S/0U/0?) | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0209 | 2 / -1 |
| `F3_tseitin_expander_sat` | 300 | 100.0% (3S/0U/0?) | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0737 | 2 / -1 |
| `F3_tseitin_expander_sat` | 600 | 100.0% (3S/0U/0?) | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.2909 | 2 / -1 |
| `F3_tseitin_expander_unsat` | 150 | 100.0% (0S/3U/0?) | 100.0% (0S/3U/0?) | **100.0%** (0S/3U/0?) | 0.0002 | 1 / 0 |
| `F3_tseitin_expander_unsat` | 300 | 100.0% (0S/3U/0?) | 100.0% (0S/3U/0?) | **100.0%** (0S/3U/0?) | 0.0005 | 1 / 0 |
| `F3_tseitin_expander_unsat` | 600 | 100.0% (0S/3U/0?) | 100.0% (0S/3U/0?) | **100.0%** (0S/3U/0?) | 0.0012 | 1 / 0 |
| `F4_3sat_high_girth` | 150 | 100.0% (5S/0U/0?) | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0049 | 2 / 0 |
| `F4_3sat_high_girth` | 300 | 60.0% (3S/0U/2?) | 60.0% (3S/0U/2?) | **100.0%** (3S/2U/0?) | 0.1039 | 2 / 0 |
| `F4_3sat_high_girth` | 600 | 60.0% (3S/0U/2?) | 60.0% (3S/0U/2?) | **60.0%** (3S/0U/2?) | 0.3459 | 2 / -1 |
| `F5_pigeonhole` | 150 | 0.0% (0S/0U/2?) | 100.0% (0S/2U/0?) | **100.0%** (0S/2U/0?) | 0.0007 | 2 / 0 |
| `F5_pigeonhole` | 300 | 0.0% (0S/0U/2?) | 100.0% (0S/2U/0?) | **100.0%** (0S/2U/0?) | 0.0025 | 2 / 0 |
| `F5_pigeonhole` | 600 | 0.0% (0S/0U/2?) | 100.0% (0S/2U/0?) | **100.0%** (0S/2U/0?) | 0.0067 | 2 / 0 |

- **Layer 2 (72 high-scale):** `VERIFIED_SAT=44`, `VERIFIED_UNSAT=2`, `UNRESOLVED=26`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `1.631s`
- **Layer 2.5 (72 high-scale):** `VERIFIED_SAT=49`, `VERIFIED_UNSAT=12`, `UNRESOLVED=11`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `1.796s`
- **Layer 2.75 (72 high-scale):** `VERIFIED_SAT=49`, `VERIFIED_UNSAT=18`, `UNRESOLVED=5`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `1.151s`
- **Layer 2.8 (72 high-scale):** `VERIFIED_SAT=49`, `VERIFIED_UNSAT=20`, `UNRESOLVED=3`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, `OVERFLOW=0`, runtime `5.951s`
