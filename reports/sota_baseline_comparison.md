# External SOTA Baseline Comparison (90 Instances: 72 High-Scale + 18 Coupled `F6`)

- **Per-instance timeout:** `10.0s`
- **External solvers:** `CaDiCaL 1.9.5` (DIMACS CNF), `CryptoMiniSat 5.18.0` (DIMACS CNF), `Z3 5.4.1` (`PbEq` OPB)
- **Note on RoundingSat:** Omitted cleanly due to missing local `cmake`/`boost >= 1.70` C++ build dependencies (per fallback plan).

## 1. Overall Summary (72 High-Scale `F1`–`F5` and 18 Coupled `F6`)

| Solver | Input | High-Scale 72 (`F1`–`F5`) | High-Scale Time | Coupled `F6` (/18) | `F6` UNSAT (/9) | `F6` Time | Certification / TCB |
|---|---|---:|---:|---:|---:|---:|---|
| **Ours: Layer 2.75 (`GadgetSP+CP`)** | Native 1-in-3 | 67/72 (93.1%) | 1.151s | 17/18 (94.4%) | 8/9 | 0.308s | Pure-kernel Lean 4 (`by decide`) |
| **Ours: Layer 2.8 (`+FLE/NG/WS`)** | Native 1-in-3 | 69/72 (95.8%) | 5.951s | 17/18 (94.4%) | 8/9 | 2.046s | Pure-kernel Lean 4 + Rust subproof |
| **CaDiCaL_1.9.5** | `DIMACS_CNF` | 72/72 (100.0%) | 0.318s | 18/18 (100.0%) | 9/9 | 0.006s | External LRAT/DRAT (uncertified here) |
| **CryptoMiniSat_5** | `DIMACS_CNF` | 72/72 (100.0%) | 2.699s | 18/18 (100.0%) | 9/9 | 0.529s | Uncertified (FRAT/DRAT optional) |
| **Z3_PB_OPB** | `OPB_PbEq` | 72/72 (100.0%) | 1.489s | 18/18 (100.0%) | 9/9 | 0.102s | Uncertified SMT/PB |

## 2. Per-Family Breakdown (Solved / Total, Wall-Clock Time)

| Family | Total | Ours L2.8 | CaDiCaL 1.9.5 | CryptoMiniSat 5 | Z3 (OPB `PbEq`) |
|---|---:|---|---|---|---|
| `F1_random_crit` | 18 | 17/18 (1.477s) | 18/18 (0.011s) | 18/18 (0.773s) | 18/18 (0.134s) |
| `F2_planted_hard` | 15 | 15/15 (1.018s) | 15/15 (0.001s) | 15/15 (0.264s) | 15/15 (0.086s) |
| `F3_tseitin_expander_sat` | 9 | 9/9 (1.157s) | 9/9 (0.001s) | 9/9 (0.243s) | 9/9 (0.049s) |
| `F3_tseitin_expander_unsat` | 9 | 9/9 (0.006s) | 9/9 (0.054s) | 9/9 (0.286s) | 9/9 (0.175s) |
| `F4_3sat_high_girth` | 15 | 13/15 (2.273s) | 15/15 (0.003s) | 15/15 (0.549s) | 15/15 (0.086s) |
| `F5_pigeonhole` | 6 | 6/6 (0.020s) | 6/6 (0.247s) | 6/6 (0.584s) | 6/6 (0.957s) |
| `F6_hybrid_f2_z_sat` | 9 | 9/9 (1.680s) | 9/9 (0.001s) | 9/9 (0.248s) | 9/9 (0.043s) |
| `F6_hybrid_f2_z_unsat` | 9 | 8/9 (0.366s) | 9/9 (0.005s) | 9/9 (0.281s) | 9/9 (0.059s) |
