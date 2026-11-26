# Monotone 1-in-3 SAT: PD-PFGC Candidate Algorithm & Falsification Harness

Self-contained pure Python 3.11 standard-library implementation and empirical falsification study of **PD-PFGC (Primal-Dual Polyrhythmic Fisher-Rao Geodesic Collapse)** for Monotone (Positive) 1-in-3 SAT across instance sizes $n \in \{15, 30, 60\}$.

## Integrity & Isolation Guarantees

- **Zero external solver delegation**: The solver (`src/monotone_1in3/solver.py` and `src/monotone_1in3/primitives.py`) uses **only** Python 3.11 standard-library arithmetic instrumented via `bitwidth.py`. It does not import or invoke any external SAT, CSP, LP, or ILP solver (`pysat`, `z3`, `ortools`, `scipy`, etc.), nor does it import the harness-only DPLL oracle in `generators.py`.
- **Independent deterministic verification**: Every candidate assignment returned as `SAT` is checked by `src/monotone_1in3/verifier.py`, which shares no solver logic and deterministically validates `{0, 1}` integer domain membership and exact clause sum `x[a] + x[b] + x[c] == 1` for every clause.
- **Explicit bit-width tracking**: All solver arithmetic runs through `BitLedger`-tracked scalar types (`TrackedInt`, `TrackedFloat`, `TrackedFraction`, `TrackedDecimal`) recording integer `bit_length()`, rational numerator/denominator bit-widths, IEEE-754 `float64` dynamic-range span `(max_exp - min_exp) + 53`, cancellation loss, overflow/subnormal/NaN counters, and operation counts.

## Directory Layout

- `docs/ALGORITHM_SPEC.md` — Formal mathematical specification, per-iteration operation count, bit-width & conditioning bounds, and theoretical falsification hypotheses.
- `src/monotone_1in3/` — Core package (`instance.py`, `verifier.py`, `bitwidth.py`, `primitives.py`, `solver.py`, `generators.py`, `harness.py`).
- `tests/` — Unit tests (`test_verifier.py`, `test_bitwidth.py`, `test_math_identities.py`, `test_generators.py`, `test_solver_smoke.py`).
- `reports/` — Generated empirical outputs (`results.json`, `results.csv`, `evaluation_report.md`).

## Running Tests & Empirical Harness

Use Python 3.11+ (pure stdlib):

```zsh
# Run full unit test suite
PYTHONPATH=src python3 -m unittest discover -s tests -v

# Run fast smoke evaluation (50 instances)
PYTHONPATH=src python3 -m monotone_1in3.harness --fast

# Run full 140-instance benchmark suite (writes reports/results.json, results.csv, evaluation_report.md)
PYTHONPATH=src python3 -m monotone_1in3.harness
```
