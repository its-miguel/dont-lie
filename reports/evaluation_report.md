# PD-PFGC Empirical Falsification & Evaluation Report

## 1. Execution Summary
- **Suite mode:** `full` (140 instances, seed `20261124`)
- **Total wall-clock runtime:** `71.376s` (budget `< 120s`)
- **Overall outcome counts:** `VERIFIED_SAT=63`, `VERIFIED_UNSAT=9`, `UNRESOLVED=68`, `OVERFLOW=0`, `FALSE_SAT_CLAIM=0`, `FALSE_UNSAT_CLAIM=0`
- **Soundness audit:** `FALSE_SAT_CLAIM + FALSE_UNSAT_CLAIM = 0` (independent deterministic verifier `verifier.py` confirmed zero false SAT claims and zero false UNSAT certificates).

## 2. Per-Family and Per-Size Performance ($n \in \{15, 30, 60\}$)

| Family | $n$ | Total (SAT/UNSAT) | Verified SAT Rate | Verified UNSAT Rate | Unresolved Rate | Timeout Rate | Med/Max Iters | Med/Max Time (s) | Med $r_\infty$ | Med Integrality Gap | Trapped $\approx \frac{1}{3}\mathbf{1}$ | Max Int Bits (Bound) | Max Float Exp / Dyn-Range Bits |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `F1_random` | 15 | 20 (16/4) | 87.5% | 100.0% | 10.0% | 10.0% | 44.5 / 301 | 0.0758 / 0.4516 | 0.4115 | 0.4531 | 0 | 3 (7) | 55 / 192 |
| `F1_random` | 30 | 20 (13/7) | 61.5% | 57.1% | 40.0% | 40.0% | 147.5 / 212 | 0.5046 / 0.7091 | 0.498 | 0.4378 | 0 | 3 (8) | 31 / 199 |
| `F1_random` | 60 | 20 (12/8) | 16.7% | 12.5% | 85.0% | 85.0% | 129.0 / 149 | 1.0534 / 1.0937 | 0.5259 | 0.4585 | 0 | 4 (9) | 30 / 250 |
| `F2_planted_sat` | 15 | 10 (10/0) | 90.0% | — | 10.0% | 10.0% | 9.0 / 226 | 0.0116 / 0.4538 | 0.2746 | 0.4508 | 0 | 3 (7) | 50 / 163 |
| `F2_planted_sat` | 30 | 10 (10/0) | 80.0% | — | 20.0% | 20.0% | 16.0 / 189 | 0.0649 / 0.7039 | 0.3406 | 0.4642 | 0 | 3 (8) | 30 / 185 |
| `F2_planted_sat` | 60 | 10 (10/0) | 40.0% | — | 60.0% | 60.0% | 124.0 / 150 | 1.053 / 1.0941 | 0.3862 | 0.4505 | 0 | 3 (9) | 30 / 252 |
| `F3a_tseitin_sat` | 15 | 5 (5/0) | 100.0% | — | 0.0% | 0.0% | 6.0 / 60 | 0.0105 / 0.103 | 0.2323 | 0.4677 | 0 | 3 (7) | 29 / 198 |
| `F3a_tseitin_sat` | 30 | 5 (5/0) | 100.0% | — | 0.0% | 0.0% | 50.0 / 173 | 0.1715 / 0.6369 | 0.4436 | 0.4849 | 0 | 4 (8) | 30 / 215 |
| `F3a_tseitin_sat` | 60 | 5 (5/0) | 40.0% | — | 60.0% | 60.0% | 133.0 / 145 | 1.0502 / 1.0537 | 0.4878 | 0.4346 | 0 | 3 (9) | 30 / 258 |
| `F3b_tseitin_unsat` | 15 | 5 (0/5) | — | 0.0% | 100.0% | 100.0% | 264.0 / 274 | 0.4512 / 0.452 | 0.558 | 0.3757 | 0 | 3 (7) | 36 / 161 |
| `F3b_tseitin_unsat` | 30 | 5 (0/5) | — | 0.0% | 100.0% | 100.0% | 198.0 / 202 | 0.701 / 0.7016 | 0.4798 | 0.4301 | 0 | 4 (8) | 30 / 191 |
| `F3b_tseitin_unsat` | 60 | 5 (0/5) | — | 0.0% | 100.0% | 100.0% | 122.0 / 144 | 1.0534 / 1.056 | 0.3558 | 0.4018 | 0 | 4 (9) | 31 / 226 |
| `F4a_3sat_sat` | 15 | 5 (5/0) | 80.0% | — | 20.0% | 20.0% | 1.0 / 232 | 0.0019 / 0.4509 | 0.2281 | 0.4551 | 0 | 3 (7) | 38 / 164 |
| `F4a_3sat_sat` | 30 | 5 (5/0) | 40.0% | — | 60.0% | 60.0% | 158.0 / 201 | 0.7016 / 0.7029 | 0.4693 | 0.4796 | 0 | 3 (8) | 30 / 213 |
| `F4a_3sat_sat` | 60 | 5 (5/0) | 0.0% | — | 100.0% | 100.0% | 121.0 / 129 | 1.0562 / 1.0979 | 0.481 | 0.3821 | 0 | 4 (9) | 31 / 211 |
| `F4b_3sat_unsat` | 60 | 5 (0/5) | — | 0.0% | 100.0% | 100.0% | 121.0 / 127 | 1.0544 / 1.1221 | 0.4789 | 0.4426 | 0 | 3 (9) | 31 / 208 |

## 3. Scaling Exponent Analysis ($n = 15 \to 30 \to 60$)

| Family | $\beta_{15\to 30}$ | $\beta_{30\to 60}$ | $\beta_{15\to 60}$ | Timeout Rate (15/30/60) | Unresolved Rate @ $n=60$ | Falsification Flag |
|---|---:|---:|---:|---:|---:|---|
| `F1_random` | 1.729 | TIMEOUT_CENSORED | TIMEOUT_CENSORED | 10.0% / 40.0% / 85.0% | 85.0% | TIMEOUT_CENSORED, HIGH_UNRESOLVED_AT_60 |
| `F2_planted_sat` | 0.83 | TIMEOUT_CENSORED | TIMEOUT_CENSORED | 10.0% / 20.0% / 60.0% | 60.0% | TIMEOUT_CENSORED, HIGH_UNRESOLVED_AT_60 |
| `F3a_tseitin_sat` | 3.059 | TIMEOUT_CENSORED | TIMEOUT_CENSORED | 0.0% / 0.0% / 60.0% | 60.0% | TIMEOUT_CENSORED, HIGH_UNRESOLVED_AT_60 |
| `F3b_tseitin_unsat` | TIMEOUT_CENSORED | TIMEOUT_CENSORED | TIMEOUT_CENSORED | 100.0% / 100.0% / 100.0% | 100.0% | TIMEOUT_CENSORED, HIGH_UNRESOLVED_AT_60 |
| `F4a_3sat_sat` | TIMEOUT_CENSORED | TIMEOUT_CENSORED | TIMEOUT_CENSORED | 20.0% / 60.0% / 100.0% | 100.0% | TIMEOUT_CENSORED, HIGH_UNRESOLVED_AT_60 |
| `F4b_3sat_unsat` | None | None | None | — / — / 100.0% | 100.0% | TIMEOUT_CENSORED, HIGH_UNRESOLVED_AT_60 |

> **Timeout Censoring Note:** Fixed wall-clock caps (`0.45s / 0.70s / 1.05s` for $n=15/30/60$) truncate iterations once `timeout_rate > 50%`. Any $\beta$ pair where either size has `timeout_rate > 50%` is marked `TIMEOUT_CENSORED` rather than reporting negative wall-clock truncation artifacts as sub-constant algorithmic scaling.

## 4. Precision-Escalation Bit-Width Comparison (`float64` vs `Decimal` vs `Fraction`)

| Instance | Mode | Status | Iters | Max Int Bits | Max Fraction Bits | Float/Dec Phys Bits | Max Float Exp | Dyn-Range Bits | Guardrail |
|---|---|---|---:|---:|---:|---:|---:|---:|---|
| `K4_3_UNSAT` | `float64` | `UNSAT_CERTIFIED` | 9 | 2 | 0 | 64 | 29 | 134 | None |
| `K4_3_UNSAT` | `decimal_prec80` | `UNSAT_CERTIFIED` | 9 | 2 | 0 | 282 | 28 | 346 | None |
| `K4_3_UNSAT` | `fraction_limit2048` | `OVERFLOW` | 0 | 1784 | 3566 | 0 | None | 0 | Fraction bit-width 3566 exceeded limit 2048 |
| `F2_n15_m9_SAT` | `float64` | `SAT` | 1 | 3 | 0 | 64 | 29 | 146 | None |
| `F2_n15_m9_SAT` | `decimal_prec80` | `SAT` | 1 | 3 | 0 | 282 | 28 | 386 | None |
| `F2_n15_m9_SAT` | `fraction_limit2048` | `OVERFLOW` | 0 | 1784 | 3566 | 0 | None | 0 | Fraction bit-width 3566 exceeded limit 2048 |

> **Fraction Probe Note:** Under `fraction_limit2048`, `K4_3_UNSAT` (`fraction_ops=54`, `iterations=0`), `F2_n15_m9_SAT` (`fraction_ops=290`, `iterations=0`) tripped the 2048-bit guardrail during $t=0$ Cholesky precomputation (`cholesky_factor(M0)` via 4-step Newton `_fraction_sqrt` and rational squaring in `primitives.py:257-260`), before iteration 0 started. The $O(3^t)$ rational iteration blowup is separately isolated in `tests/test_bitwidth.py::test_tracked_fraction_exponential_growth_and_limit`.

## 5. Empirical Diagnosis: Where PD-PFGC Succeeds vs. Breaks

1. **Soundness & Verifier Discipline:** Across all 140 instances, `FALSE_SAT_CLAIM = 0` and `FALSE_UNSAT_CLAIM = 0`. Every SAT assignment returned by PD-PFGC passed the independent `{0, 1}` exact-sum verifier.
2. **Success Regimes:**
   - **Planted SAT (`F2_planted_sat` at $n=60$):** Achieved `40.0%` verified SAT solve rate with median `124.0` iterations, showing that when a degree-balanced planted solution exists, $M_0^{-1}$, $\Phi_{\mathrm{WF}}$, and $\mathcal{F}_{\mathrm{spec}}$ often separate $S_1$ from $S_0$ within the sub-second budget.
   - **Tseitin XOR SAT (`F3a_tseitin_sat` at $n=60$):** Achieved `40.0%` verified SAT solve rate (median `133.0` iterations).
   - **Rank-1 Quadratic-Infeasible Core (`K4^3` probe):** Certified `UNSAT_CERTIFIED` deterministically via $\mathcal{D}_{\mathrm{spec}} > \epsilon_{\mathrm{cert}}$.
3. **Breakage & Falsification Regimes:**
   - **Degree-2 Shor-1 Integrality Gap on Structured UNSAT (`F3b_tseitin_unsat`, `F4b_3sat_unsat`, and random UNSAT):** `F3b` at $n=60$ had `0.0%` UNSAT certification and `100.0%` unresolved; `F4b` at $n=60$ had `0.0%` certification and `100.0%` unresolved. Because Tseitin XOR parity and sparse 3-SAT gadgets remain feasible under degree-2 moment relaxations, weak duality prevents $\mathcal{D}_{\mathrm{spec}} > 0$ from firing.
   - **Critical-Threshold Random SAT & Coupled 3-SAT Gadgets at $n=60$:** `F1_random` SAT solve rate at $n=60$ dropped to `16.7%` (unresolved `85.0%`) and `F4a_3sat_sat` at $n=60$ dropped to `0.0%` (unresolved `100.0%`), demonstrating metastable phase frustration and time/iteration budget saturation as $n$ scales from $15 \to 60$.
4. **Bit-Width Bounds Compliance vs. Dynamic-Range Decay & Rational Blowup:**
   - In clamped `float64` mode, `max_int_bit_width` stayed strictly within the static bound $\lceil \log_2(9m + 1) \rceil$, and `max_float_exp` remained bounded at $O(\log m)$ (observed `max_float_exp <= 55`) with zero overflows or NaNs.
   - However, in unquantized IEEE-754 `float64`, `max_dynamic_range_bits` (`(e_max - e_min) + 53`) grew up to `258` bits (`min_float_nonzero_exp` down to `-175`) as damped momenta and near-zero coordinates decayed toward negative exponents—matching the distinction in `docs/ALGORITHM_SPEC.md` §6.3 between bounded `max_float_exp`/fixed-point width $q + O(\log m)$ and unquantized `float64` $e_{\min}$ decay.
   - In contrast, exact `Fraction` mode (`fraction_limit2048`) tripped the 2048-bit guardrail at `iterations=0` (`54` fraction ops on `K4_3_UNSAT`) during $t=0$ Cholesky precomputation (`cholesky_factor(M0)` via 4-step Newton `_fraction_sqrt` and rational squaring in `primitives.py:257-260`), before iteration 0 started, while `tests/test_bitwidth.py` separately isolates the $O(3^t)$ polynomial iteration blowup.
