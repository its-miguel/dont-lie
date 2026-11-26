"""Independent deterministic verifier for Monotone 1-in-3 SAT.

Strictly isolated from solver.py, primitives.py, bitwidth.py, and generators.py.
"""

from __future__ import annotations

from collections.abc import Sequence
from dataclasses import dataclass
from typing import Any

from .instance import Monotone1in3Instance


@dataclass(frozen=True)
class VerificationResult:
    """Result returned by the independent deterministic Monotone 1-in-3 SAT verifier."""

    is_valid_input: bool
    is_sat: bool
    total_clauses: int
    satisfied_count: int
    violated_clauses: tuple[tuple[int, tuple[int, int, int], int], ...]
    error_message: str = ""


def _is_strict_int(val: Any) -> bool:
    return isinstance(val, int) and not isinstance(val, bool)


def _is_strict_binary_int(val: Any) -> bool:
    return _is_strict_int(val) and (val == 0 or val == 1)


def verify_raw(
    n_vars: int,
    clauses: Sequence[tuple[int, int, int]],
    assignment: Sequence[int],
) -> VerificationResult:
    """Deterministically verify a candidate {0,1}^n assignment against raw clauses."""
    if not _is_strict_int(n_vars) or n_vars < 0:
        return VerificationResult(
            is_valid_input=False,
            is_sat=False,
            total_clauses=0,
            satisfied_count=0,
            violated_clauses=(),
            error_message=f"n_vars must be a non-negative strict int, got {n_vars!r} ({type(n_vars).__name__})",
        )

    if isinstance(clauses, (str, bytes, bytearray)) or not isinstance(clauses, Sequence):
        return VerificationResult(
            is_valid_input=False,
            is_sat=False,
            total_clauses=0,
            satisfied_count=0,
            violated_clauses=(),
            error_message=f"Clauses must be a sequence, got {type(clauses).__name__}",
        )

    total = len(clauses)
    if isinstance(assignment, (str, bytes, bytearray)) or not isinstance(assignment, Sequence):
        return VerificationResult(
            is_valid_input=False,
            is_sat=False,
            total_clauses=total,
            satisfied_count=0,
            violated_clauses=(),
            error_message=f"Assignment must be a sequence, got {type(assignment).__name__}",
        )

    if len(assignment) != n_vars:
        return VerificationResult(
            is_valid_input=False,
            is_sat=False,
            total_clauses=total,
            satisfied_count=0,
            violated_clauses=(),
            error_message=f"Expected length {n_vars}, got {len(assignment)}",
        )

    for idx, val in enumerate(assignment):
        if not _is_strict_binary_int(val):
            return VerificationResult(
                is_valid_input=False,
                is_sat=False,
                total_clauses=total,
                satisfied_count=0,
                violated_clauses=(),
                error_message=(
                    f"Entry at index {idx} must be strict int 0 or 1, "
                    f"got {val!r} ({type(val).__name__})"
                ),
            )

    satisfied = 0
    violated: list[tuple[int, tuple[int, int, int], int]] = []
    for c_idx, clause in enumerate(clauses):
        if isinstance(clause, (str, bytes, bytearray)) or not isinstance(clause, Sequence) or len(clause) != 3:
            return VerificationResult(
                is_valid_input=False,
                is_sat=False,
                total_clauses=total,
                satisfied_count=0,
                violated_clauses=(),
                error_message=f"Clause {c_idx} must be a 3-element sequence, got {clause!r}",
            )
        a, b, c = clause
        if not (_is_strict_int(a) and _is_strict_int(b) and _is_strict_int(c)):
            return VerificationResult(
                is_valid_input=False,
                is_sat=False,
                total_clauses=total,
                satisfied_count=0,
                violated_clauses=(),
                error_message=f"Clause {c_idx} contains non-integer variable index: {clause!r}",
            )
        if not (0 <= a < n_vars and 0 <= b < n_vars and 0 <= c < n_vars):
            return VerificationResult(
                is_valid_input=False,
                is_sat=False,
                total_clauses=total,
                satisfied_count=0,
                violated_clauses=(),
                error_message=f"Clause {c_idx} index out of range [0, {n_vars}): {clause!r}",
            )
        s = assignment[a] + assignment[b] + assignment[c]
        if s == 1:
            satisfied += 1
        else:
            violated.append((c_idx, (a, b, c), s))

    return VerificationResult(
        is_valid_input=True,
        is_sat=(len(violated) == 0),
        total_clauses=total,
        satisfied_count=satisfied,
        violated_clauses=tuple(violated),
        error_message="",
    )


def verify_assignment(
    instance: Monotone1in3Instance,
    assignment: Sequence[int],
) -> VerificationResult:
    """Deterministically verify a candidate {0,1}^n assignment against a Monotone1in3Instance."""
    return verify_raw(instance.n_vars, instance.clauses, assignment)
