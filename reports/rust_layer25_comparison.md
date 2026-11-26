# Layer 2 vs. Layer 2.5 Side-by-Side Falsification Report (`HybridGroebnerCascade` vs. `GadgetSPCascade`)

## 1. Parity Suite Validation (140 Instances, $n \in \{15, 30, 60\}$)
| Solver | `VERIFIED_SAT` (/101) | `VERIFIED_UNSAT` (/39) | `UNRESOLVED` | `FALSE_SAT` | `FALSE_UNSAT` | `OVERFLOW` | Runtime (s) |
|---|---:|---:|---:|---:|---:|---:|---:|
| **Layer 2 (`HybridGroebnerCascade`)** | 101 | 34 | 5 | 0 | 0 | 0 | 0.0287 |
| **Layer 2.5 (`GadgetSPCascade`)** | 101 | 39 | 0 | 0 | 0 | 0 | 0.0109 |

## 2. High-Scale Side-by-Side Comparison ($n \in \{150, 300, 600\}$, 72 Instances)

| Family | Target $n$ | L2 Solve Rate (S/U/?) | L2.5 Solve Rate (S/U/?) | L2 Avg Time (s) | L2.5 Avg Time (s) | L2 `max_int`/`exp` | L2.5 `max_int`/`exp` |
|---|---:|---|---|---:|---:|---|---|
| `F1_random_crit` | 150 | 100.0% (5S/1U/0?) | **100.0%** (5S/1U/0?) | 0.0015 | 0.0010 | 2 / 2 | 2 / 0 |
| `F1_random_crit` | 300 | 83.3% (4S/1U/1?) | **100.0%** (5S/1U/0?) | 0.0070 | 0.0072 | 2 / 2 | 2 / 0 |
| `F1_random_crit` | 600 | 16.7% (1S/0U/5?) | **83.3%** (4S/1U/1?) | 0.0483 | 0.0456 | 2 / 2 | 2 / 0 |
| `F2_planted_hard` | 150 | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0017 | 0.0010 | 1 / 2 | 1 / -2 |
| `F2_planted_hard` | 300 | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0048 | 0.0036 | 1 / 1 | 1 / -2 |
| `F2_planted_hard` | 600 | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0124 | 0.0142 | 1 / 2 | 1 / -2 |
| `F3_tseitin_expander_sat` | 150 | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0012 | 0.0009 | 1 / 2 | 1 / -1 |
| `F3_tseitin_expander_sat` | 300 | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0029 | 0.0021 | 2 / 2 | 1 / -1 |
| `F3_tseitin_expander_sat` | 600 | 100.0% (3S/0U/0?) | **100.0%** (3S/0U/0?) | 0.0072 | 0.0062 | 1 / 2 | 1 / -1 |
| `F3_tseitin_expander_unsat` | 150 | 0.0% (0S/0U/3?) | **100.0%** (0S/3U/0?) | 0.0134 | 0.0003 | 2 / 2 | 1 / 0 |
| `F3_tseitin_expander_unsat` | 300 | 0.0% (0S/0U/3?) | **100.0%** (0S/3U/0?) | 0.0229 | 0.0005 | 2 / 2 | 1 / 0 |
| `F3_tseitin_expander_unsat` | 600 | 0.0% (0S/0U/3?) | **100.0%** (0S/3U/0?) | 0.0745 | 0.0012 | 2 / 2 | 1 / 0 |
| `F4_3sat_high_girth` | 150 | 100.0% (5S/0U/0?) | **100.0%** (5S/0U/0?) | 0.0016 | 0.0007 | 2 / 3 | 2 / -1 |
| `F4_3sat_high_girth` | 300 | 60.0% (3S/0U/2?) | **60.0%** (3S/0U/2?) | 0.0064 | 0.0175 | 2 / 2 | 2 / -1 |
| `F4_3sat_high_girth` | 600 | 40.0% (2S/0U/3?) | **60.0%** (3S/0U/2?) | 0.0254 | 0.0879 | 2 / 3 | 2 / -1 |
| `F5_pigeonhole` | 150 | 0.0% (0S/0U/2?) | **0.0%** (0S/0U/2?) | 0.0308 | 0.0263 | 2 / 2 | 2 / -1 |
| `F5_pigeonhole` | 300 | 0.0% (0S/0U/2?) | **0.0%** (0S/0U/2?) | 0.0699 | 0.1255 | 2 / 3 | 1 / -1 |
| `F5_pigeonhole` | 600 | 0.0% (0S/0U/2?) | **0.0%** (0S/0U/2?) | 0.2326 | 0.2626 | 2 / 3 | 2 / -1 |

## 3. Overall Totals & Scaling Exponents ($\beta_{150 \to 600} = \log(\text{ops}_{600} / \text{ops}_{150}) / \log(n_{600} / n_{150})$)

| Family | L2 $\beta_{150 \to 600}$ | L2.5 $\beta_{150 \to 600}$ | L2 Solve @ 600 | L2.5 Solve @ 600 | Delta @ 600 |
|---|---:|---:|---:|---:|---:|
| `F1_random_crit` | 1.82 | 3.57 | 16.7% | **83.3%** | +66.7% |
| `F2_planted_hard` | 0.61 | 1.81 | 100.0% | **100.0%** | +0.0% |
| `F3_tseitin_expander_sat` | 0.53 | 1.18 | 100.0% | **100.0%** | +0.0% |
| `F3_tseitin_expander_unsat` | 0.31 | 1.85 | 0.0% | **100.0%** | +100.0% |
| `F4_3sat_high_girth` | 1.21 | 3.59 | 40.0% | **60.0%** | +20.0% |
| `F5_pigeonhole` | 0.48 | 1.55 | 0.0% | **0.0%** | +0.0% |

- **Layer 2 Overall (72 high-scale):** `VERIFIED_SAT=44`, `VERIFIED_UNSAT=2`, `UNRESOLVED=26`, runtime `1.635s`
- **Layer 2.5 Overall (72 high-scale):** `VERIFIED_SAT=49`, `VERIFIED_UNSAT=12`, `UNRESOLVED=11`, `FALSE_SAT=0`, `FALSE_UNSAT=0`, runtime `1.809s`
