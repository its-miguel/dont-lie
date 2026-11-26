# Layer 2 (Rust) High-Scale Falsification Report (`HybridGroebnerCascade`: Track C + Track D)

## 1. Parity Validation against Run #1/#2 Python Suite (140 Instances, $n \in \{15, 30, 60\}$)
- **VERIFIED_SAT:** `101 / 101` (100.0%)
- **VERIFIED_UNSAT (independently proof-checked):** `34 / 39` (87.2%)
- **UNRESOLVED:** `5`
- **Soundness:** `FALSE_SAT = 0`, `FALSE_UNSAT = 0`, `OVERFLOW = 0`
- **Total Parity Suite Runtime:** `0.0293s` (vs. `7.64s` in Python Track C and `71.38s` in Run #1)

## 2. High-Scale Adversarial Falsification ($n \in \{150, 300, 600\}$)

| Family | Target $n$ | Avg Actual $n$ | Total | `VERIFIED_SAT` | `VERIFIED_UNSAT` | `UNRESOLVED` | Avg Total Ops | Avg S-Poly | Avg `LDL^T` Ops | Avg Time (s) | `max_int_bits` | `max_float_exp` | Peak Mem (KB) |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `F1_random_crit` | 150 | 150.0 | 6 | 5 | 1 | 0 | 1368023 | 8712 | 1242234 | 0.0016 | 2 | 2 | 154.0 |
| `F1_random_crit` | 300 | 300.0 | 6 | 4 | 1 | 1 | 2908522 | 85890 | 625907 | 0.0071 | 2 | 2 | 187.3 |
| `F1_random_crit` | 600 | 600.0 | 6 | 1 | 0 | 5 | 17030077 | 724639 | 0 | 0.0481 | 2 | 2 | 291.5 |
| `F2_planted_hard` | 150 | 150.0 | 5 | 5 | 0 | 0 | 2179749 | 5688 | 1894806 | 0.0019 | 1 | 2 | 154.0 |
| `F2_planted_hard` | 300 | 300.0 | 5 | 5 | 0 | 0 | 3366480 | 61450 | 1594171 | 0.0047 | 1 | 1 | 187.3 |
| `F2_planted_hard` | 600 | 600.0 | 5 | 5 | 0 | 0 | 5059098 | 229080 | 0 | 0.0125 | 1 | 2 | 291.5 |
| `F3_tseitin_expander_sat` | 150 | 154.0 | 3 | 3 | 0 | 0 | 1310007 | 8416 | 1130311 | 0.0013 | 1 | 2 | 154.8 |
| `F3_tseitin_expander_sat` | 300 | 306.0 | 3 | 3 | 0 | 0 | 1376332 | 49704 | 414652 | 0.0030 | 2 | 2 | 188.9 |
| `F3_tseitin_expander_sat` | 600 | 610.0 | 3 | 3 | 0 | 0 | 2732013 | 133720 | 397370 | 0.0070 | 1 | 2 | 295.0 |
| `F3_tseitin_expander_unsat` | 150 | 154.0 | 3 | 0 | 0 | 3 | 20419227 | 75369 | 18581830 | 0.0141 | 2 | 2 | 154.8 |
| `F3_tseitin_expander_unsat` | 300 | 306.0 | 3 | 0 | 0 | 3 | 15093824 | 342033 | 8003026 | 0.0235 | 2 | 2 | 188.9 |
| `F3_tseitin_expander_unsat` | 600 | 610.0 | 3 | 0 | 0 | 3 | 31182159 | 1337153 | 5062713 | 0.0748 | 2 | 2 | 295.0 |
| `F4_3sat_high_girth` | 150 | 154.0 | 5 | 5 | 0 | 0 | 1669631 | 10579 | 1323523 | 0.0017 | 2 | 3 | 154.9 |
| `F4_3sat_high_girth` | 300 | 306.0 | 5 | 3 | 0 | 2 | 2303215 | 85673 | 26215 | 0.0066 | 2 | 2 | 189.0 |
| `F4_3sat_high_girth` | 600 | 610.0 | 5 | 2 | 0 | 3 | 8836289 | 385625 | 184408 | 0.0250 | 2 | 3 | 295.2 |
| `F5_pigeonhole` | 150 | 143.0 | 2 | 0 | 0 | 2 | 51337310 | 143542 | 47707858 | 0.0316 | 2 | 2 | 153.3 |
| `F5_pigeonhole` | 300 | 334.0 | 2 | 0 | 0 | 2 | 38458479 | 1544238 | 10461594 | 0.0720 | 2 | 3 | 200.3 |
| `F5_pigeonhole` | 600 | 637.0 | 2 | 0 | 0 | 2 | 105802674 | 5795231 | 3538170 | 0.2278 | 2 | 3 | 304.1 |

## 3. Empirical Scaling Exponents ($\beta = \log(\text{ops}_2 / \text{ops}_1) / \log(n_2 / n_1)$)

| Family | $\beta_{150 \to 300}$ | $\beta_{300 \to 600}$ | $\beta_{150 \to 600}$ | Solve Rate @ 150 | Solve Rate @ 300 | Solve Rate @ 600 | Regime Diagnosis |
|---|---:|---:|---:|---:|---:|---:|---|
| `F1_random_crit` | 1.09 | 2.55 | 1.82 | 100.0% | 83.3% | 16.7% | DEGRADATION / STALL THRESHOLD (increasing UNRESOLVED as n scales) |
| `F2_planted_hard` | 0.63 | 0.59 | 0.61 | 100.0% | 100.0% | 100.0% | Solved 100% @ n=600 (polynomial ops) |
| `F3_tseitin_expander_sat` | 0.07 | 0.99 | 0.53 | 100.0% | 100.0% | 100.0% | Solved 100% @ n=600 (polynomial ops) |
| `F3_tseitin_expander_unsat` | -0.44 | 1.05 | 0.31 | 0.0% | 0.0% | 0.0% | BOUNDED-DEGREE BARRIER (0% solved — hits UNRESOLVED across all scales) |
| `F4_3sat_high_girth` | 0.47 | 1.95 | 1.21 | 100.0% | 60.0% | 40.0% | DEGRADATION / STALL THRESHOLD (increasing UNRESOLVED as n scales) |
| `F5_pigeonhole` | -0.34 | 1.57 | 0.48 | 0.0% | 0.0% | 0.0% | BOUNDED-DEGREE BARRIER (0% solved — hits UNRESOLVED across all scales) |
