"""Immutable Monotone 1-in-3 SAT instance representation and sparse incidence builder."""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Iterable, Sequence


def _is_strict_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


@dataclass(frozen=True)
class Monotone1in3Instance:
    """Immutable representation of a Monotone 1-in-3 SAT formula.

    Variables are 0-indexed in ``[0, n_vars)``. Each clause ``(a, b, c)``
    requires ``x[a] + x[b] + x[c] == 1`` for ``x in {0, 1}^n_vars``.
    """

    n_vars: int
    clauses: tuple[tuple[int, int, int], ...]
    metadata: dict[str, Any] = field(default_factory=dict)

    def __post_init__(self) -> None:
        if not _is_strict_int(self.n_vars) or self.n_vars < 0:
            raise ValueError(f"n_vars must be a non-negative integer, got {self.n_vars!r}")

        normalized: list[tuple[int, int, int]] = []
        for idx, clause in enumerate(self.clauses):
            if not isinstance(clause, (tuple, list)) or len(clause) != 3:
                raise ValueError(f"Clause {idx} must have length 3, got {clause!r}")
            a, b, c = clause
            if not (_is_strict_int(a) and _is_strict_int(b) and _is_strict_int(c)):
                raise ValueError(f"Clause {idx} contains non-integer variable index: {clause!r}")
            if not (0 <= a < self.n_vars and 0 <= b < self.n_vars and 0 <= c < self.n_vars):
                raise ValueError(
                    f"Clause {idx} variable index out of range [0, {self.n_vars}): {clause!r}"
                )
            normalized.append((a, b, c))

        object.__setattr__(self, "clauses", tuple(normalized))
        object.__setattr__(self, "metadata", dict(self.metadata))

    @property
    def m_clauses(self) -> int:
        return len(self.clauses)

    def has_distinct_literals(self) -> bool:
        """Return True iff every clause has 3 distinct variable indices."""
        return all(len({a, b, c}) == 3 for a, b, c in self.clauses)

    def has_duplicate_clauses(self) -> bool:
        """Return True iff any two clauses represent the same unordered literal multiset."""
        seen: set[tuple[int, int, int]] = set()
        for a, b, c in self.clauses:
            key = tuple(sorted((a, b, c)))
            if key in seen:
                return True
            seen.add(key)  # type: ignore[arg-type]
        return False

    def validate_hygiene(self) -> tuple[bool, list[str]]:
        """Validate strict distinct-literal and no-duplicate-clause hygiene invariants."""
        errors: list[str] = []
        seen: set[tuple[int, int, int]] = set()
        for idx, (a, b, c) in enumerate(self.clauses):
            if len({a, b, c}) != 3:
                errors.append(f"Clause {idx} has repeated variable: {(a, b, c)}")
            key = (min(a, b, c), a + b + c - min(a, b, c) - max(a, b, c), max(a, b, c))
            if key in seen:
                errors.append(f"Duplicate unordered clause at index {idx}: {(a, b, c)}")
            seen.add(key)
        return (len(errors) == 0, errors)


@dataclass(frozen=True)
class SparseIncidence:
    """Sparse representation of the clause-variable incidence matrix A in {0,1,2,3}^{m x n}."""

    n_vars: int
    m_clauses: int
    clauses: tuple[tuple[int, int, int], ...]
    clause_terms: tuple[tuple[tuple[int, int], ...], ...]
    var_clauses: tuple[tuple[tuple[int, int], ...], ...]
    degrees: tuple[int, ...]
    max_degree: int

    def compute_ata_matrix(self) -> list[list[int]]:
        """Return exact integer matrix A^T A in Z^{n x n}."""
        n = self.n_vars
        mat = [[0] * n for _ in range(n)]
        for terms in self.clause_terms:
            for i, ci in terms:
                row = mat[i]
                for k, ck in terms:
                    row[k] += ci * ck
        return mat

    def compute_k_matrix(self) -> list[list[int]]:
        """Return exact integer conflict matrix K = A^T A - diag(d) in Z^{n x n}."""
        mat = self.compute_ata_matrix()
        for i in range(self.n_vars):
            mat[i][i] -= self.degrees[i]
        return mat


def build_incidence(instance: Monotone1in3Instance) -> SparseIncidence:
    """Construct sparse incidence structures for A, A^T, and degrees d = A^T 1."""
    n = instance.n_vars
    m = instance.m_clauses
    degrees = [0] * n
    var_lists: list[list[tuple[int, int]]] = [[] for _ in range(n)]
    clause_terms_list: list[tuple[tuple[int, int], ...]] = []

    for c_idx, (a, b, c) in enumerate(instance.clauses):
        counts: dict[int, int] = {}
        counts[a] = counts.get(a, 0) + 1
        counts[b] = counts.get(b, 0) + 1
        counts[c] = counts.get(c, 0) + 1
        terms = tuple(sorted(counts.items()))
        clause_terms_list.append(terms)
        for v_idx, coeff in terms:
            degrees[v_idx] += coeff
            var_lists[v_idx].append((c_idx, coeff))

    max_deg = max(degrees) if degrees else 0
    return SparseIncidence(
        n_vars=n,
        m_clauses=m,
        clauses=instance.clauses,
        clause_terms=tuple(clause_terms_list),
        var_clauses=tuple(tuple(vl) for vl in var_lists),
        degrees=tuple(degrees),
        max_degree=max_deg,
    )
