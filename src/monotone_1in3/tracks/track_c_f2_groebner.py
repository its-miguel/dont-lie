"""Track C: Modular F_2 Linear + Bounded Degree-3 Boolean Groebner Dual Certificate.

Augments the square-root-free LDL^T PD-PFGC primal-dual solver with two exact,
1-bit-width algebraic UNSAT certifiers over F_2[x_0, ..., x_{n-1}] / <x_i^2 + x_i>:
  1. Exact F_2 Linear Gaussian Elimination (RREF on A x = 1 mod 2) using explicit
     0/1 row vectors (1-bit entries recorded in BitLedger, zero denominator blowup).
  2. Coupled Degree-2/3 Boolean Groebner / Nullstellensatz ideal closure combining
     linear RREF equivalences, quadratic annihilators (x_a x_b = 0), pair S-polynomials,
     clause-literal multiplications, degree-3 S-polynomial transitivity, and bounded
     degree-3 sparse F_2 Macaulay/Groebner reduction.
  3. Primal integration: feeds algebraic constants, equivalences, and quadratic
     constraints into guided rounding and square-root-free LDL^T PD-PFGC + D_spec.

Strictly isolated from generators.py, harness.py, and external SAT/CSP/ILP solvers.
Every SAT assignment MUST pass verify_assignment(instance, assign) from verifier.py.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
import math
import time
from typing import Any, Sequence

from ..bitwidth import (
    BitLedger,
    BitWidthExceededError,
    TrackedScalar,
    make_scalar,
    t_acos,
    t_cos,
    t_fmod_2pi,
    t_pi,
    t_sin,
    t_sqrt,
)
from ..instance import Monotone1in3Instance, SparseIncidence, build_incidence
from ..primitives import (
    LDLTFactor,
    SparseOperators,
    build_M0,
    build_M_cert,
    clamp_scalar,
    greedy_conflict_round,
    is_finite_scalar,
    is_zero_scalar,
    ldlt_factor,
    ldlt_solve,
    threshold_round,
    walsh_fourier_clause_eval,
)
from ..solver import SolverConfig, SolverResult, _compute_primal_metrics
from ..verifier import verify_assignment


# ---------------------------------------------------------------------------
# Component 1: Exact 1-bit F_2 Linear System (Incremental RREF)
# ---------------------------------------------------------------------------

class _F2LinearSystem:
    """Exact F_2 linear system over explicit 0/1 row vectors (strictly 1-bit entries)."""

    def __init__(self, n_vars: int, ledger: BitLedger) -> None:
        self.n = n_vars
        self.ledger = ledger
        # pivot_col -> list[int] of length n + 1 (last entry is RHS in {0, 1})
        self.pivots: dict[int, list[int]] = {}
        self.inconsistent: bool = False
        self.rank: int = 0

    def _xor_rows(self, dst: list[int], src: list[int]) -> None:
        ledger = self.ledger
        for k in range(self.n + 1):
            sk = src[k]
            if sk:
                val = dst[k] ^ 1
                dst[k] = val
                ledger.record_int(val, count_op=True)

    def add_equation(self, coeffs: list[int], rhs: int) -> bool:
        """Add sum_i coeffs[i] * x_i = rhs (mod 2). Returns False iff 1 = 0 derived."""
        if self.inconsistent:
            return False
        n = self.n
        row = [c & 1 for c in coeffs]
        row.append(rhs & 1)
        self.ledger.record_int(row[n], count_op=True)

        # Reduce against existing pivots
        for pcol, prow in self.pivots.items():
            if row[pcol]:
                self._xor_rows(row, prow)

        # Find first nonzero variable column
        piv = -1
        for c in range(n):
            if row[c]:
                piv = c
                break

        if piv == -1:
            if row[n]:
                self.inconsistent = True
                return False
            return True

        # Back-eliminate piv from all existing pivot rows to maintain RREF
        for pcol, prow in self.pivots.items():
            if prow[piv]:
                self._xor_rows(prow, row)

        self.pivots[piv] = row
        self.rank = len(self.pivots)
        return True

    def add_sparse_equation(self, var_indices: Sequence[int], rhs: int) -> bool:
        """Add XOR of var_indices = rhs (mod 2)."""
        coeffs = [0] * self.n
        for v in var_indices:
            coeffs[v] ^= 1
            self.ledger.record_int(coeffs[v], count_op=True)
        return self.add_equation(coeffs, rhs)

    def extract_affine_relations(
        self,
    ) -> tuple[list[tuple[int, int]], list[tuple[int, int, int]], list[tuple[int, int, int, int]]]:
        """Extract all 1-var constants, 2-var equivalences, and 3-var linear equations from RREF.

        Returns:
            constants: list of (var, val) meaning x_var = val
            equivalences: list of (u, v, diff) meaning x_u ^ x_v = diff
            triples: list of (a, b, c, rhs) meaning x_a ^ x_b ^ x_c = rhs
        """
        n = self.n
        constants: list[tuple[int, int]] = []
        equivalences: list[tuple[int, int, int]] = []
        triples: list[tuple[int, int, int, int]] = []
        # Map free-column support signature -> (pivot_col, rhs) to detect x_p1 ^ x_p2 = c1 ^ c2
        sig_map: dict[tuple[int, ...], tuple[int, int]] = {}

        for pcol, row in self.pivots.items():
            rhs = row[n]
            free_cols: list[int] = []
            for c in range(n):
                if c != pcol and row[c]:
                    free_cols.append(c)
            k = len(free_cols)
            if k == 0:
                constants.append((pcol, rhs))
            elif k == 1:
                equivalences.append((pcol, free_cols[0], rhs))
            else:
                if k == 2:
                    triples.append((pcol, free_cols[0], free_cols[1], rhs))
                sig = tuple(free_cols)
                prev = sig_map.get(sig)
                if prev is not None:
                    p0, r0 = prev
                    equivalences.append((p0, pcol, r0 ^ rhs))
                else:
                    sig_map[sig] = (pcol, rhs)

        return constants, equivalences, triples

    def evaluate_subspace_point(self, free_values: dict[int, int] | None = None) -> list[int]:
        """Evaluate a point in the F_2 affine subspace {x : A x = 1 mod 2}."""
        n = self.n
        x = [0] * n
        if free_values:
            for v, val in free_values.items():
                if v not in self.pivots:
                    x[v] = val & 1
        for pcol, row in self.pivots.items():
            acc = row[n]
            for c in range(n):
                if c != pcol and row[c] and x[c]:
                    acc ^= 1
                    self.ledger.record_int(acc, count_op=True)
            x[pcol] = acc
        return x


# ---------------------------------------------------------------------------
# Component 2: Coupled Degree-2/3 Boolean Groebner Ideal Closure over F_2
# ---------------------------------------------------------------------------

def _lit(var: int, neg: int) -> int:
    """Encode literal: (var, 0) -> 2*var (x_v), (var, 1) -> 2*var + 1 (1 + x_v)."""
    return (var << 1) | (neg & 1)


class _BooleanIdealClosure:
    """Exact polynomial-time Boolean ideal closure over F_2[x]/<x_i^2 + x_i>.

    Maintains:
      - F_2 linear RREF system
      - Canonical parity union-find (x_i = x_root ^ flip) and fixed constants
      - Degree-2 binomial ideal Q: pairs (l1, l2) representing l1 * l2 = 0
      - Degree-3 S-polynomial transitivity & clause-literal multiplication
      - Bounded degree-3 sparse F_2 Macaulay/Groebner reduction
    """

    def __init__(self, instance: Monotone1in3Instance, ledger: BitLedger) -> None:
        self.instance = instance
        self.n = instance.n_vars
        self.m = instance.m_clauses
        self.ledger = ledger
        self.f2 = _F2LinearSystem(self.n, ledger)

        # Parity union-find: x_i = x_{parent[i]} ^ flip[i]
        self.parent: list[int] = list(range(self.n))
        self.flip: list[int] = [0] * self.n
        self.fixed: list[int | None] = [None] * self.n

        # Degree-2 binomials: adj[l] = set of literals l2 such that l * l2 = 0
        self.adj: list[set[int]] = [set() for _ in range(2 * self.n)]
        self.bin_queue: deque[tuple[int, int]] = deque()
        self.seen_bins: set[tuple[int, int]] = set()

        self.inconsistent: bool = False
        self.cert_reason: str = ""
        self._linear_dirty: bool = False
        self._stage_label: str = "F2_LINEAR_UNSAT_CERT"

    def find(self, v: int) -> tuple[int, int]:
        """Return (root, parity) such that x_v = x_root ^ parity."""
        if self.parent[v] == v:
            return v, 0
        root, p = self.find(self.parent[v])
        self.parent[v] = root
        self.flip[v] ^= p
        return root, self.flip[v]

    def get_fixed(self, v: int) -> int | None:
        """Return forced Boolean value of x_v if known, else None."""
        r, p = self.find(v)
        fv = self.fixed[r]
        if fv is None:
            return None
        return fv ^ p

    def set_fixed(self, v: int, val: int, add_to_f2: bool = True) -> bool:
        """Assert x_v = val in the ideal. Returns False iff 1 = 0 derived."""
        if self.inconsistent:
            return False
        val &= 1
        self.ledger.record_int(val, count_op=True)
        r, p = self.find(v)
        target = val ^ p
        cur = self.fixed[r]
        if cur is not None:
            if cur != target:
                self.inconsistent = True
                if not self.cert_reason:
                    self.cert_reason = self._stage_label
                return False
            return True

        self.fixed[r] = target
        self._linear_dirty = True
        if add_to_f2:
            if not self.f2.add_sparse_equation((r,), target):
                self.inconsistent = True
                if not self.cert_reason:
                    self.cert_reason = self._stage_label
                return False

        # Propagate x_r = target through existing degree-2 binomials:
        # If l_true = lit(r, 1 ^ target) == 1, then every l2 in adj[l_true] must be 0.
        l_true = _lit(r, 1 ^ target)
        for l2 in list(self.adj[l_true]):
            v2 = l2 >> 1
            neg2 = l2 & 1
            # l2 = x_{v2} ^ neg2 = 0 => x_{v2} = neg2
            if not self.set_fixed(v2, neg2, add_to_f2=True):
                return False
        return True

    def set_equiv(self, u: int, v: int, diff: int, add_to_f2: bool = True) -> bool:
        """Assert x_u ^ x_v = diff in the ideal. Returns False iff 1 = 0 derived."""
        if self.inconsistent:
            return False
        diff &= 1
        self.ledger.record_int(diff, count_op=True)
        ru, pu = self.find(u)
        rv, pv = self.find(v)
        d = diff ^ pu ^ pv

        if ru == rv:
            if d:
                self.inconsistent = True
                if not self.cert_reason:
                    self.cert_reason = self._stage_label
                return False
            return True

        fu = self.fixed[ru]
        fv = self.fixed[rv]
        if fu is not None and fv is not None:
            if (fu ^ fv) != d:
                self.inconsistent = True
                if not self.cert_reason:
                    self.cert_reason = self._stage_label
                return False
            return True

        # Canonical merge: smaller root stays root
        if rv < ru:
            ru, rv = rv, ru
            fu, fv = fv, fu

        self.parent[rv] = ru
        self.flip[rv] = d
        self._linear_dirty = True

        if add_to_f2:
            if not self.f2.add_sparse_equation((ru, rv), d):
                self.inconsistent = True
                if not self.cert_reason:
                    self.cert_reason = self._stage_label
                return False

        if fu is None and fv is not None:
            if not self.set_fixed(ru, fv ^ d, add_to_f2=True):
                return False
        elif fu is not None and fv is None:
            self.fixed[rv] = fu ^ d

        # Transfer degree-2 binomials from rv to ru (x_rv = x_ru ^ d)
        for neg_v in (0, 1):
            old_lit = _lit(rv, neg_v)
            new_lit = _lit(ru, neg_v ^ d)
            neighbors = list(self.adj[old_lit])
            for nb in neighbors:
                if not self.add_binomial(new_lit, nb):
                    return False

        return True

    def _canonical_lit(self, lit_id: int) -> tuple[int | None, int]:
        """Resolve literal to (const_val_or_None, canonical_lit_id)."""
        v = lit_id >> 1
        neg = lit_id & 1
        r, p = self.find(v)
        fv = self.fixed[r]
        if fv is not None:
            return (fv ^ p ^ neg), -1
        return None, _lit(r, neg ^ p)

    def add_binomial(self, l1: int, l2: int) -> bool:
        """Assert l1 * l2 = 0 in the Boolean ideal. Returns False iff 1 = 0 derived."""
        if self.inconsistent:
            return False
        c1, cl1 = self._canonical_lit(l1)
        c2, cl2 = self._canonical_lit(l2)

        if c1 is not None:
            if c1 == 0:
                return True
            # 1 * l2 = 0
            if c2 is not None:
                if c2 == 1:
                    self.inconsistent = True
                    if not self.cert_reason:
                        self.cert_reason = "GROEBNER_QUAD_CONFLICT"
                    return False
                return True
            return self.set_fixed(cl2 >> 1, cl2 & 1, add_to_f2=True)

        if c2 is not None:
            if c2 == 0:
                return True
            return self.set_fixed(cl1 >> 1, cl1 & 1, add_to_f2=True)

        if cl1 == cl2:
            # l^2 = l = 0 => x_r = neg
            return self.set_fixed(cl1 >> 1, cl1 & 1, add_to_f2=True)
        if cl1 == (cl2 ^ 1):
            # l * (1 + l) = 0 (tautology)
            return True

        pair = (cl1, cl2) if cl1 < cl2 else (cl2, cl1)
        if pair in self.seen_bins:
            return True

        self.seen_bins.add(pair)
        self.adj[cl1].add(cl2)
        self.adj[cl2].add(cl1)
        self.bin_queue.append(pair)
        self.ledger.record_int(1, count_op=True)

        # Degree-2 pair S-polynomials on the same pair of variables:
        # 1) cl1 * cl2 = 0 and cl1 * (1 + cl2) = 0 => cl1 = 0
        if (cl2 ^ 1) in self.adj[cl1]:
            if not self.set_fixed(cl1 >> 1, cl1 & 1, add_to_f2=True):
                return False
        # 2) cl1 * cl2 = 0 and (1 + cl1) * cl2 = 0 => cl2 = 0
        if (cl1 ^ 1) in self.adj[cl2]:
            if not self.set_fixed(cl2 >> 1, cl2 & 1, add_to_f2=True):
                return False
        # 3) cl1 * cl2 = 0 and (1 + cl1) * (1 + cl2) = 0 => cl1 + cl2 = 1
        if (cl2 ^ 1) in self.adj[cl1 ^ 1]:
            v1, n1 = cl1 >> 1, cl1 & 1
            v2, n2 = cl2 >> 1, cl2 & 1
            # (x_v1 ^ n1) ^ (x_v2 ^ n2) = 1 => x_v1 ^ x_v2 = 1 ^ n1 ^ n2
            if not self.set_equiv(v1, v2, 1 ^ n1 ^ n2, add_to_f2=True):
                return False

        return not self.inconsistent

    def _drain_binomial_transitivity(self, step_budget: int) -> bool:
        """Degree-3 S-polynomial transitivity: S-poly(l1*l2, (1+l2)*l3) = l1*l3 = 0."""
        steps = 0
        while self.bin_queue and steps < step_budget:
            l1, l2 = self.bin_queue.popleft()
            c1, cl1 = self._canonical_lit(l1)
            c2, cl2 = self._canonical_lit(l2)
            if c1 is not None or c2 is not None or cl1 == cl2 or cl1 == (cl2 ^ 1):
                if not self.add_binomial(l1, l2):
                    return False
                continue

            # S-poly with (cl2 ^ 1) * l3 = 0 => cl1 * l3 = 0
            for l3 in list(self.adj[cl2 ^ 1]):
                steps += 1
                if not self.add_binomial(cl1, l3):
                    return False
                if steps >= step_budget:
                    break
            if self.inconsistent or steps >= step_budget:
                break

            # S-poly with (cl1 ^ 1) * l3 = 0 => cl2 * l3 = 0
            for l3 in list(self.adj[cl1 ^ 1]):
                steps += 1
                if not self.add_binomial(cl2, l3):
                    return False
                if steps >= step_budget:
                    break
            if self.inconsistent:
                break
        return not self.inconsistent

    def _propagate_clause_multiplications(
        self,
        extra_triples: Sequence[tuple[int, int, int, int]],
    ) -> bool:
        """Multiply 3-var linear equations (x_a + x_b + x_c + d = 0) by literals l_u.

        If l_u * x_a = c_a * l_u and l_u * x_b = c_b * l_u (from degree-2 binomials),
        then l_u * (x_a + x_b + x_c + d) = 0 reduces to l_u * (x_c + (c_a ^ c_b ^ d)) = 0,
        a new degree-2 binomial (or degree-1 linear equation if l_u involves x_c)!
        """
        eqs: list[tuple[int, int, int, int]] = [(a, b, c, 1) for (a, b, c) in self.instance.clauses]
        eqs.extend(extra_triples)

        for a, b, c, rhs in eqs:
            # Canonicalize the 3-var equation
            lits_raw = [a, b, c]
            d = rhs & 1
            roots: list[int] = []
            for v in lits_raw:
                r, p = self.find(v)
                fv = self.fixed[r]
                if fv is not None:
                    d ^= (fv ^ p)
                else:
                    d ^= p
                    roots.append(r)

            # Cancel duplicate roots mod 2
            reduced: list[int] = []
            for r in roots:
                if r in reduced:
                    reduced.remove(r)
                else:
                    reduced.append(r)

            k = len(reduced)
            if k == 0:
                if d:
                    self.inconsistent = True
                    if not self.cert_reason:
                        self.cert_reason = "GROEBNER_CLAUSE_CONFLICT"
                    return False
                continue
            if k == 1:
                if not self.set_fixed(reduced[0], d, add_to_f2=True):
                    return False
                continue
            if k == 2:
                if not self.set_equiv(reduced[0], reduced[1], d, add_to_f2=True):
                    return False
                continue

            # k == 3: x_{r0} + x_{r1} + x_{r2} = d (mod 2)
            r0, r1, r2 = reduced[0], reduced[1], reduced[2]
            # For each pair (ri, rj) and remaining rk, find literals l_u adjacent to both ri and rj
            for ri, rj, rk in ((r0, r1, r2), (r0, r2, r1), (r1, r2, r0)):
                # l_u in adj[lit(ri, 0)] => l_u * x_ri = 0 (c_i = 0)
                # l_u in adj[lit(ri, 1)] => l_u * (1 + x_ri) = 0 => l_u * x_ri = l_u (c_i = 1)
                for ci in (0, 1):
                    si = self.adj[_lit(ri, ci)]
                    if not si:
                        continue
                    for cj in (0, 1):
                        sj = self.adj[_lit(rj, cj)]
                        if not sj:
                            continue
                        common = si & sj if len(si) <= len(sj) else sj & si
                        if not common:
                            continue
                        # l_u * x_rk + (ci ^ cj ^ d) * l_u = 0
                        # If (ci ^ cj ^ d) == 0: l_u * x_rk = 0 -> (l_u, lit(rk, 0))
                        # If (ci ^ cj ^ d) == 1: l_u * (1 + x_rk) = 0 -> (l_u, lit(rk, 1))
                        target_lit = _lit(rk, ci ^ cj ^ d)
                        for lu in list(common):
                            if not self.add_binomial(lu, target_lit):
                                return False
        return not self.inconsistent

    def _run_bounded_deg3_macaulay(self) -> tuple[bool, bool]:
        """Bounded degree-3 sparse F_2 Groebner / Macaulay elimination.

        Builds a polynomial-size basis of degree <= 3 polynomials over F_2[x]/<x_i^2 + x_i>
        from active reduced clauses and degree-2 binomials, performs grevlex sparse F_2
        Gaussian elimination, and checks for 1 = 0 or newly derived linear equations.

        Returns:
            (consistent, derived_new_linear)
        """
        if self.inconsistent:
            return False, False

        # Collect active canonical clauses (3 unfixed roots)
        active_clauses: list[tuple[int, int, int, int]] = []
        active_vars: set[int] = set()
        for a, b, c in self.instance.clauses:
            d = 1
            roots: list[int] = []
            for v in (a, b, c):
                r, p = self.find(v)
                fv = self.fixed[r]
                if fv is not None:
                    d ^= (fv ^ p)
                else:
                    d ^= p
                    roots.append(r)
            reduced: list[int] = []
            for r in roots:
                if r in reduced:
                    reduced.remove(r)
                else:
                    reduced.append(r)
            if len(reduced) == 3:
                t = tuple(sorted(reduced))
                active_clauses.append((t[0], t[1], t[2], d))
                active_vars.update(t)

        if not active_clauses:
            return True, False

        # Build sparse polynomials as frozenset of sorted variable-index tuples
        # () = constant 1, (i,) = x_i, (i, j) = x_i x_j, (i, j, k) = x_i x_j x_k
        max_polys = min(4 * self.m * max(1, self.n), 450)
        polys: list[frozenset[tuple[int, ...]]] = []

        def _mul_var(poly: frozenset[tuple[int, ...]], v: int) -> frozenset[tuple[int, ...]]:
            out: set[tuple[int, ...]] = set()
            for mon in poly:
                if v in mon:
                    nm = mon
                else:
                    nm = tuple(sorted(mon + (v,)))
                if len(nm) > 3:
                    return frozenset()  # Exceeds degree-3 cap
                if nm in out:
                    out.remove(nm)
                else:
                    out.add(nm)
                self.ledger.record_int(1, count_op=True)
            return frozenset(out)

        # 1. Add active clause linear polys and their quadratic annihilators
        var_to_clauses: dict[int, list[int]] = {}
        for idx, (r0, r1, r2, d) in enumerate(active_clauses):
            mons: set[tuple[int, ...]] = {(r0,), (r1,), (r2,)}
            if d:
                mons.add(())
            polys.append(frozenset(mons))
            for rv in (r0, r1, r2):
                var_to_clauses.setdefault(rv, []).append(idx)

        # 2. Add active canonical degree-2 binomials
        active_var_list = sorted(active_vars)
        active_set = set(active_var_list)
        added_pairs: set[tuple[int, int]] = set()
        for r in active_var_list:
            for neg_r in (0, 1):
                lr = _lit(r, neg_r)
                for l2 in self.adj[lr]:
                    c2, cl2 = self._canonical_lit(l2)
                    if c2 is not None:
                        continue
                    r2 = cl2 >> 1
                    neg2 = cl2 & 1
                    if r2 not in active_set or r2 == r:
                        continue
                    key = (lr, cl2) if lr < cl2 else (cl2, lr)
                    if key in added_pairs:
                        continue
                    added_pairs.add(key)
                    # (x_r ^ neg_r) * (x_r2 ^ neg2) = x_r*x_r2 ^ neg2*x_r ^ neg_r*x_r2 ^ (neg_r & neg2)
                    mons2: set[tuple[int, ...]] = {(min(r, r2), max(r, r2))}
                    if neg2:
                        mons2.add((r,))
                    if neg_r:
                        mons2.add((r2,))
                    if neg_r and neg2:
                        mons2.add(())
                    polys.append(frozenset(mons2))
                    if len(polys) >= max_polys:
                        break
                if len(polys) >= max_polys:
                    break
            if len(polys) >= max_polys:
                break

        # 3. Generate degree-2/3 Macaulay multiples: multiply each active clause by
        #    neighboring active variables (variables sharing a clause or binomial)
        for r0, r1, r2, d in active_clauses:
            if len(polys) >= max_polys:
                break
            base_mons: set[tuple[int, ...]] = {(r0,), (r1,), (r2,)}
            if d:
                base_mons.add(())
            base_p = frozenset(base_mons)
            # Collect neighbor variables
            nbrs: set[int] = set()
            for rv in (r0, r1, r2):
                for c_idx in var_to_clauses.get(rv, ())[:4]:
                    ca, cb, cc, _ = active_clauses[c_idx]
                    nbrs.add(ca)
                    nbrs.add(cb)
                    nbrs.add(cc)
            for nv in sorted(nbrs):
                if len(polys) >= max_polys:
                    break
                mp = _mul_var(base_p, nv)
                if mp:
                    polys.append(mp)

        # 4. Sparse F_2 Gaussian elimination ordered by grevlex (highest degree first)
        # Pivot dict: leading_monomial -> polynomial
        basis: dict[tuple[int, ...], frozenset[tuple[int, ...]]] = {}

        def _lead_mon(poly: frozenset[tuple[int, ...]]) -> tuple[int, ...]:
            return max(poly, key=lambda mon: (len(mon), mon))

        derived_linear = False
        elim_steps = 0
        max_elim_steps = 4000

        for poly in polys:
            cur = poly
            while cur and elim_steps < max_elim_steps:
                lm = _lead_mon(cur)
                piv = basis.get(lm)
                if piv is None:
                    basis[lm] = cur
                    # Check if constant 1 = 0
                    if lm == ():
                        self.inconsistent = True
                        self.cert_reason = "GROEBNER_DEG3_UNSAT_CERT"
                        return False, False
                    # Check if new degree-1 linear polynomial
                    if len(lm) == 1:
                        lin_vars = [m[0] for m in cur if len(m) == 1]
                        rhs_lin = 1 if () in cur else 0
                        if len(lin_vars) == 1:
                            if not self.set_fixed(lin_vars[0], rhs_lin, add_to_f2=True):
                                return False, False
                            derived_linear = True
                        elif len(lin_vars) == 2:
                            if not self.set_equiv(lin_vars[0], lin_vars[1], rhs_lin, add_to_f2=True):
                                return False, False
                            derived_linear = True
                        else:
                            if not self.f2.add_sparse_equation(lin_vars, rhs_lin):
                                self.inconsistent = True
                                self.cert_reason = "GROEBNER_DEG3_UNSAT_CERT"
                                return False, False
                            self._linear_dirty = True
                            derived_linear = True
                    break
                cur = cur ^ piv
                elim_steps += 1
                self.ledger.record_int(1, count_op=True)
            if self.inconsistent or elim_steps >= max_elim_steps:
                break

        return not self.inconsistent, derived_linear

    def run_closure(self) -> bool:
        """Execute full Stage 1 (F_2 RREF) + Stage 2 (Deg-2/3 Groebner closure).

        Returns True if consistent (possibly with forced vars/equivalences),
        False if 1 = 0 was soundly derived in the ideal (UNSAT_CERTIFIED).
        """
        # Step 1: Load all clauses into F_2 linear system and quadratic annihilators
        for a, b, c in self.instance.clauses:
            # Linear equation: x_a ^ x_b ^ x_c = 1
            if not self.f2.add_sparse_equation((a, b, c), 1):
                self.inconsistent = True
                self.cert_reason = "F2_LINEAR_UNSAT_CERT"
                return False

        # Initial RREF check already certifies pure F_2 linear UNSAT (e.g. Tseitin UNSAT)
        if self.f2.inconsistent:
            self.inconsistent = True
            self.cert_reason = "F2_LINEAR_UNSAT_CERT"
            return False

        # Transition to Stage 2: Coupled F_2 RREF + Degree-2/3 Boolean Groebner ideal closure
        self._stage_label = "GROEBNER_DEG23_UNSAT_CERT"

        # Add pairwise quadratic annihilators x_a x_b = 0, x_b x_c = 0, x_a x_c = 0
        for a, b, c in self.instance.clauses:
            if not self.add_binomial(_lit(a, 0), _lit(b, 0)):
                return False
            if not self.add_binomial(_lit(b, 0), _lit(c, 0)):
                return False
            if not self.add_binomial(_lit(a, 0), _lit(c, 0)):
                return False

        # Iterative fixed point: F_2 RREF <-> Degree-2/3 binomial & clause multiplication
        max_rounds = max(4, self.n + 2)
        trans_budget = max(2000, 4 * self.n * self.n)
        for _ in range(max_rounds):
            self._linear_dirty = False
            prev_bins = len(self.seen_bins)

            # Extract all constants, equivalences, and 3-var equations from RREF
            constants, equivs, triples = self.f2.extract_affine_relations()
            for v, val in constants:
                if not self.set_fixed(v, val, add_to_f2=False):
                    return False
            for u, v, diff in equivs:
                if not self.set_equiv(u, v, diff, add_to_f2=False):
                    return False

            # Degree-3 S-polynomial transitivity on binomials
            if not self._drain_binomial_transitivity(trans_budget):
                return False

            # Multiply clauses + RREF triples by literals
            if not self._propagate_clause_multiplications(triples):
                return False

            # Drain any newly created binomials
            if not self._drain_binomial_transitivity(trans_budget):
                return False

            if not self._linear_dirty and len(self.seen_bins) == prev_bins:
                break

        # Final bounded degree-3 sparse Macaulay/Groebner pass (at most 2 outer rounds)
        self._stage_label = "GROEBNER_DEG3_MACAULAY_UNSAT_CERT"
        for _ in range(2):
            ok, derived_lin = self._run_bounded_deg3_macaulay()
            if not ok:
                return False
            if not derived_lin:
                break
            # Re-run fast linear-binomial fixed point on newly derived linear equations
            constants, equivs, triples = self.f2.extract_affine_relations()
            for v, val in constants:
                if not self.set_fixed(v, val, add_to_f2=False):
                    return False
            for u, v, diff in equivs:
                if not self.set_equiv(u, v, diff, add_to_f2=False):
                    return False
            if not self._drain_binomial_transitivity(trans_budget):
                return False
            if not self._propagate_clause_multiplications(triples):
                return False
            if not self._drain_binomial_transitivity(trans_budget):
                return False

        # Sanity check: if all variables are fixed, verify against clauses;
        # any violation is an immediate 1 = 0 certificate!
        all_fixed = all(self.get_fixed(i) is not None for i in range(self.n))
        if all_fixed:
            assign = [int(self.get_fixed(i) or 0) for i in range(self.n)]
            ver = verify_assignment(self.instance, assign)
            if not ver.is_sat:
                self.inconsistent = True
                self.cert_reason = "GROEBNER_UNIQUE_POINT_UNSAT"
                return False

        return not self.inconsistent


# ---------------------------------------------------------------------------
# Component 3: Square-Root-Free LDL^T Dual Certificate & Guided Rounding
# ---------------------------------------------------------------------------

def _evaluate_dual_certificate_ldlt(
    y_cert: Sequence[TrackedScalar],
    s_cert: Sequence[TrackedScalar],
    factor_cert: LDLTFactor,
    ops: SparseOperators,
    compute_grad_s: bool = True,
) -> tuple[
    TrackedScalar,
    list[TrackedScalar],
    list[TrackedScalar],
    list[TrackedScalar],
    list[TrackedScalar],
]:
    """Evaluate D_spec(y, s), x_dual(y, s), b(y, s), grad_y, grad_s via LDL^T."""
    n = ops.n
    m = ops.m
    at_y = ops.apply_AT(y_cert)
    b_vec: list[TrackedScalar] = []
    neg_half_b: list[TrackedScalar] = []
    neg_half = make_scalar(-0.5, ops.ledger, mode=ops.mode, decimal_prec=ops.decimal_prec)

    for i in range(n):
        bi = at_y[i] - ops.two * ops.degrees_s[i] - s_cert[i]
        b_vec.append(bi)
        neg_half_b.append(neg_half * bi)

    x_dual = ldlt_solve(factor_cert, neg_half_b)

    y_sum = ops.zero
    for yj in y_cert:
        y_sum = y_sum + yj

    quad_term = ops.zero
    for i in range(n):
        quad_term = quad_term + x_dual[i] * neg_half_b[i]

    m_scalar = make_scalar(m, ops.ledger, mode=ops.mode, decimal_prec=ops.decimal_prec)
    d_spec = m_scalar - y_sum - quad_term

    ax_dual = ops.apply_A(x_dual)
    grad_y = [ax_dual[j] - ops.one for j in range(m)]
    grad_s = [x_dual[i] * x_dual[i] - x_dual[i] for i in range(n)] if compute_grad_s else []
    return d_spec, x_dual, b_vec, grad_y, grad_s


def _ldlt_diag_margins(
    factor: LDLTFactor,
    ledger: BitLedger,
    mode: str = "float64",
    decimal_prec: int = 80,
) -> list[TrackedScalar]:
    """Square-root-free single-coordinate PD margins mu_i = 1 / ((L D L^T)^{-1})_{ii}."""
    n = factor.size
    zero = make_scalar(0, ledger, mode=mode, decimal_prec=decimal_prec)
    one = make_scalar(1, ledger, mode=mode, decimal_prec=decimal_prec)
    margins: list[TrackedScalar] = []
    for i in range(n):
        u = [zero] * n
        u[i] = one
        w = one / factor.D[i]
        for r in range(i + 1, n):
            s = zero
            for k, l_rk in factor.offdiag_nz[r]:
                if k >= i:
                    s = s + l_rk * u[k]
            ur = -s
            u[r] = ur
            if not is_zero_scalar(ur):
                w = w + (ur * ur) / factor.D[r]
        margins.append(one / w)
    return margins


def _algebraic_guided_round(
    scores: Sequence[float],
    closure: _BooleanIdealClosure,
    inc: SparseIncidence,
) -> list[int]:
    """Conflict- and equivalence-aware greedy rounding respecting ideal closure."""
    n = inc.n_vars
    m = inc.m_clauses
    assigned: list[int | None] = [None] * n
    clause_hits = [0] * m

    # 1. Apply all algebraically forced constants first
    for i in range(n):
        fv = closure.get_fixed(i)
        if fv is not None:
            assigned[i] = fv
            if fv == 1:
                for c_idx, coeff in inc.var_clauses[i]:
                    clause_hits[c_idx] += coeff

    # 2. Group remaining unfixed variables by canonical root
    root_members: dict[int, list[tuple[int, int]]] = {}
    for i in range(n):
        if assigned[i] is None:
            r, p = closure.find(i)
            root_members.setdefault(r, []).append((i, p))

    # Score each root by average affinity for setting x_root = 1
    root_scores: list[tuple[float, int]] = []
    for r, members in root_members.items():
        s = 0.0
        for v, p in members:
            s += (1.0 - scores[v]) if p else scores[v]
        root_scores.append((s / len(members), r))
    root_scores.sort(key=lambda item: (-item[0], item[1]))

    def _can_set_root(r: int, val: int) -> bool:
        # Check clause hits for all members that become 1
        local_hits: dict[int, int] = {}
        for v, p in root_members[r]:
            vv = val ^ p
            if vv == 1:
                for c_idx, coeff in inc.var_clauses[v]:
                    if coeff > 1 or clause_hits[c_idx] + local_hits.get(c_idx, 0) + coeff > 1:
                        return False
                    local_hits[c_idx] = local_hits.get(c_idx, 0) + coeff
        return True

    def _assign_root(r: int, val: int) -> None:
        for v, p in root_members[r]:
            vv = val ^ p
            assigned[v] = vv
            if vv == 1:
                for c_idx, coeff in inc.var_clauses[v]:
                    clause_hits[c_idx] += coeff

    # 3. Greedy assignment with degree-2 implication propagation
    for _, r in root_scores:
        if assigned[r] is not None:
            continue
        # Prefer 1 if feasible, else 0
        chosen = 1 if _can_set_root(r, 1) else 0
        _assign_root(r, chosen)
        # Propagate degree-2 binomials from l_true = lit(r, 1 ^ chosen)
        l_true = _lit(r, 1 ^ chosen)
        for l2 in closure.adj[l_true]:
            c2, cl2 = closure._canonical_lit(l2)
            if c2 is not None:
                continue
            r2 = cl2 >> 1
            neg2 = cl2 & 1
            if r2 in root_members and assigned[r2] is None:
                # cl2 = 0 => x_r2 = neg2
                if _can_set_root(r2, neg2):
                    _assign_root(r2, neg2)

    return [0 if a is None else a for a in assigned]


# ---------------------------------------------------------------------------
# Main Entry Point: solve_track_c
# ---------------------------------------------------------------------------

def solve_track_c(
    instance: Monotone1in3Instance,
    config: SolverConfig | None = None,
) -> SolverResult:
    """Solve Monotone 1-in-3 SAT via F_2 RREF + Degree-3 Boolean Groebner + LDL^T PD-PFGC."""
    t_start = time.perf_counter()
    cfg = config or SolverConfig()
    n = instance.n_vars
    m = instance.m_clauses

    ledger = BitLedger(
        max_int_bits_limit=cfg.max_int_bits_limit,
        max_fraction_bits_limit=cfg.max_fraction_bits_limit,
        raise_on_guardrail=True,
    )
    mode = cfg.mode
    dprec = cfg.decimal_prec

    # Trivial edge cases
    if m == 0:
        zero_assign = tuple([0] * n)
        ver = verify_assignment(instance, zero_assign)
        return SolverResult(
            status="SAT" if ver.is_sat else "UNRESOLVED",
            assignment=zero_assign if ver.is_sat else None,
            dual_certificate_value=0.0,
            iterations=0,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=0.0,
            primal_res_l2=0.0,
            integrality_gap=0.0,
            dual_residual=0.0,
            clause_violation_count=len(ver.violated_clauses),
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=ver,
            best_candidate=zero_assign,
            termination_reason="SAT_FOUND" if ver.is_sat else "UNRESOLVED",
            final_x=tuple(0.0 for _ in range(n)),
            max_kappa2_cert_bound=1.0,
        )

    if n == 0:
        return SolverResult(
            status="UNSAT_CERTIFIED",
            assignment=None,
            dual_certificate_value=float(m),
            iterations=0,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=1.0,
            primal_res_l2=1.0,
            integrality_gap=0.0,
            dual_residual=0.0,
            clause_violation_count=m,
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=None,
            best_candidate=None,
            termination_reason="UNSAT_CERT",
            final_x=(),
            max_kappa2_cert_bound=1.0,
        )

    b_s_eff_float = cfg.B_s
    try:
        # -------------------------------------------------------------------
        # Stage 1 & 2: Exact 1-bit F_2 RREF + Degree-2/3 Boolean Groebner
        # -------------------------------------------------------------------
        closure = _BooleanIdealClosure(instance, ledger)
        if not closure.run_closure():
            return SolverResult(
                status="UNSAT_CERTIFIED",
                assignment=None,
                dual_certificate_value=1.0,
                iterations=0,
                runtime_sec=time.perf_counter() - t_start,
                primal_res_inf=1.0,
                primal_res_l2=1.0,
                integrality_gap=0.0,
                dual_residual=0.0,
                clause_violation_count=m,
                bit_summary=ledger.summary(),
                iteration_history=[],
                verification=None,
                best_candidate=None,
                termination_reason=closure.cert_reason or "F2_GROEBNER_UNSAT_CERT",
                final_x=tuple(0.0 for _ in range(n)),
                max_kappa2_cert_bound=1.0,
            )

        # Quick Stage 3a: Check F_2 RREF subspace point & algebraic-guided rounding
        inc = build_incidence(instance)
        rref_pt = closure.f2.evaluate_subspace_point()
        ver_rref = verify_assignment(instance, rref_pt)
        if ver_rref.is_sat:
            return SolverResult(
                status="SAT",
                assignment=tuple(rref_pt),
                dual_certificate_value=0.0,
                iterations=0,
                runtime_sec=time.perf_counter() - t_start,
                primal_res_inf=0.0,
                primal_res_l2=0.0,
                integrality_gap=0.0,
                dual_residual=0.0,
                clause_violation_count=0,
                bit_summary=ledger.summary(),
                iteration_history=[],
                verification=ver_rref,
                best_candidate=tuple(rref_pt),
                termination_reason="SAT_F2_SUBSPACE",
                final_x=tuple(float(v) for v in rref_pt),
                max_kappa2_cert_bound=1.0,
            )

        # Try algebraic-guided rounding using degree-based scores
        deg_scores = [1.0 / (1.0 + inc.degrees[i]) for i in range(n)]
        alg_cand = _algebraic_guided_round(deg_scores, closure, inc)
        ver_alg = verify_assignment(instance, alg_cand)
        if ver_alg.is_sat:
            return SolverResult(
                status="SAT",
                assignment=tuple(alg_cand),
                dual_certificate_value=0.0,
                iterations=0,
                runtime_sec=time.perf_counter() - t_start,
                primal_res_inf=0.0,
                primal_res_l2=0.0,
                integrality_gap=0.0,
                dual_residual=0.0,
                clause_violation_count=0,
                bit_summary=ledger.summary(),
                iteration_history=[],
                verification=ver_alg,
                best_candidate=tuple(alg_cand),
                termination_reason="SAT_ALGEBRAIC_ROUND",
                final_x=tuple(float(v) for v in alg_cand),
                max_kappa2_cert_bound=1.0,
            )

        best_candidate: tuple[int, ...] | None = tuple(alg_cand)
        best_violations = len(ver_alg.violated_clauses)
        if len(ver_rref.violated_clauses) < best_violations:
            best_violations = len(ver_rref.violated_clauses)
            best_candidate = tuple(rref_pt)

        # -------------------------------------------------------------------
        # Stage 3b: Square-Root-Free LDL^T PD-PFGC + D_spec
        # -------------------------------------------------------------------
        max_iters = cfg.max_iters if cfg.max_iters is not None else min(1000, 15 * n + 100)
        b_cert = cfg.dual_update_interval if cfg.dual_update_interval is not None else max(1, n)
        t_anneal = max(1, int(0.75 * max_iters))

        ops = SparseOperators(inc, ledger, mode=mode, decimal_prec=dprec)
        one = ops.one
        zero = ops.zero
        half = ops.half
        pi_s = t_pi(ledger, mode=mode, decimal_prec=dprec)
        two_pi_s = pi_s + pi_s

        eta_0 = make_scalar(cfg.eta_0, ledger, mode=mode, decimal_prec=dprec)
        kappa_w = make_scalar(cfg.kappa_w, ledger, mode=mode, decimal_prec=dprec)
        rho = make_scalar(cfg.rho, ledger, mode=mode, decimal_prec=dprec)
        alpha_k = make_scalar(cfg.alpha_k, ledger, mode=mode, decimal_prec=dprec)
        mu_damp = make_scalar(cfg.mu_damp, ledger, mode=mode, decimal_prec=dprec)
        tau_step = make_scalar(cfg.tau_step, ledger, mode=mode, decimal_prec=dprec)
        delta_0 = make_scalar(cfg.delta_0, ledger, mode=mode, decimal_prec=dprec)
        gamma_wf = make_scalar(cfg.gamma_wf, ledger, mode=mode, decimal_prec=dprec)
        gamma_beat = make_scalar(cfg.gamma_beat, ledger, mode=mode, decimal_prec=dprec)
        beta_min_s = make_scalar(cfg.beta_min, ledger, mode=mode, decimal_prec=dprec)
        beta_span_s = make_scalar(cfg.beta_max - cfg.beta_min, ledger, mode=mode, decimal_prec=dprec)
        t_anneal_s = make_scalar(t_anneal, ledger, mode=mode, decimal_prec=dprec)
        eta_spec = make_scalar(cfg.eta_spec, ledger, mode=mode, decimal_prec=dprec)
        eps_imp_s = make_scalar(cfg.eps_imp, ledger, mode=mode, decimal_prec=dprec)
        eps_kick = make_scalar(cfg.eps_kick, ledger, mode=mode, decimal_prec=dprec)
        theta_pdhg = make_scalar(cfg.theta_pdhg, ledger, mode=mode, decimal_prec=dprec)
        eta_d = make_scalar(cfg.eta_d, ledger, mode=mode, decimal_prec=dprec)
        one_minus_damp_d = one - eta_d * make_scalar(cfg.delta_d, ledger, mode=mode, decimal_prec=dprec)
        B_lambda = make_scalar(cfg.B_lambda, ledger, mode=mode, decimal_prec=dprec)
        B_y = make_scalar(cfg.B_y, ledger, mode=mode, decimal_prec=dprec)
        B_s = make_scalar(cfg.B_s, ledger, mode=mode, decimal_prec=dprec)
        alpha_y = make_scalar(cfg.alpha_y, ledger, mode=mode, decimal_prec=dprec)
        alpha_s_s = make_scalar(cfg.alpha_s, ledger, mode=mode, decimal_prec=dprec)
        eps_chol = make_scalar(cfg.eps_chol, ledger, mode=mode, decimal_prec=dprec)
        two_eps_chol = ops.two * eps_chol
        max_deg_s = make_scalar(inc.max_degree, ledger, mode=mode, decimal_prec=dprec)
        min_s_bound = max_deg_s + two_eps_chol + one
        B_s_eff = B_s if B_s >= min_s_bound else min_s_bound
        b_s_eff_float = max(cfg.B_s, float(inc.max_degree) + 2.0 * cfg.eps_chol + 1.0)
        kappa2_bound = (18.0 * m + b_s_eff_float) / cfg.eps_chol

        m_s = make_scalar(m, ledger, mode=mode, decimal_prec=dprec)
        inv_sqrt_m_s = one / t_sqrt(m_s)
        eps_cert_floor_s = make_scalar(1e-6, ledger, mode=mode, decimal_prec=dprec)
        n_sq_s = make_scalar(n * n, ledger, mode=mode, decimal_prec=dprec)
        eps_mach_s = make_scalar(2.0**-53, ledger, mode=mode, decimal_prec=dprec)
        kappa2_bound_s = (make_scalar(18 * m, ledger, mode=mode, decimal_prec=dprec) + B_s_eff) / eps_chol
        cert_tol_coeff_s = n_sq_s * eps_mach_s * kappa2_bound_s
        budget_85 = make_scalar(0.85, ledger, mode=mode, decimal_prec=dprec)
        budget_50 = half

        omega_1 = pi_s / ops.three
        omega_2 = pi_s * half

        # Precompute M_0 = I + eta_0 A^T A = L D L^T (square-root-free)
        M0 = build_M0(ops, eta_0)
        L0_ldlt = ldlt_factor(M0, ledger, mode=mode, decimal_prec=dprec)
        if L0_ldlt is None:
            raise RuntimeError("Unexpected non-SPD M_0")

        # Initialize torus phases phi^(0), pinning algebraically fixed variables
        one_third = one / ops.three
        phi_base = t_acos(one_third)
        n_plus_1 = make_scalar(n + 1, ledger, mode=mode, decimal_prec=dprec)
        fixed_mask: list[int | None] = [closure.get_fixed(i) for i in range(n)]
        phi: list[TrackedScalar] = []
        for i in range(n):
            fv = fixed_mask[i]
            if fv == 0:
                phi.append(zero)
            elif fv == 1:
                phi.append(pi_s)
            else:
                idx_s = make_scalar(i + 1, ledger, mode=mode, decimal_prec=dprec)
                ang = (two_pi_s * idx_s) / n_plus_1
                phi.append(t_fmod_2pi(phi_base + delta_0 * t_sin(ang), mode=mode, decimal_prec=dprec))

        p = [zero] * n
        lam = [zero] * m
        x_prev: list[TrackedScalar] | None = None

        # Dual spectral certificate state via square-root-free LDL^T
        y_cert = [zero] * m
        s_cert = [
            clamp_scalar(ops.degrees_s[i] + two_eps_chol, B_s_eff)
            for i in range(n)
        ]

        M_cert_init = build_M_cert(ops, s_cert)
        L_cert: LDLTFactor | None = ldlt_factor(M_cert_init, ledger, mode=mode, decimal_prec=dprec)
        M_cert_shifted = build_M_cert(ops, s_cert, shift_diag=eps_chol)
        cert_pd_verified = ldlt_factor(M_cert_shifted, ledger, mode=mode, decimal_prec=dprec) is not None

        best_r2_norm_s: TrackedScalar | None = None
        stall_counter = 0
        best_d_spec = -math.inf
        last_res_inf = 1.0
        last_res_l2 = 1.0
        last_igap = 0.5
        last_dual_res = 0.0
        last_x: list[TrackedScalar] = [one_third] * n
        iter_history: list[dict[str, Any]] = []

        for t in range(max_iters):
            if cfg.max_time_sec is not None and (time.perf_counter() - t_start) >= cfg.max_time_sec:
                return SolverResult(
                    status="UNRESOLVED",
                    assignment=None,
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                    iterations=t,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=last_res_inf,
                    primal_res_l2=last_res_l2,
                    integrality_gap=last_igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=best_violations,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=None,
                    best_candidate=best_candidate,
                    termination_reason="TIMEOUT",
                    final_x=tuple(float(xi) for xi in last_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            ledger.begin_iteration(t)

            # 1. Manifold evaluation & residual
            sin_phi = [t_sin(ph) for ph in phi]
            sigma = [t_cos(ph) for ph in phi]
            x = [(one - sg) * half for sg in sigma]
            last_x = x

            ax = ops.apply_A(x)
            r = [ax[j] - one for j in range(m)]
            w = [one + kappa_w * (rj * rj) for rj in r]

            res_inf_s, res_l2_s, r2_norm_s, igap_s = _compute_primal_metrics(x, r, ops, inv_sqrt_m_s)
            res_inf = float(res_inf_s)
            res_l2 = float(res_l2_s)
            igap = float(igap_s)
            last_res_inf = res_inf
            last_res_l2 = res_l2
            last_igap = igap

            if not (is_finite_scalar(res_inf_s) and is_finite_scalar(res_l2_s)):
                ledger.end_iteration()
                return SolverResult(
                    status="OVERFLOW",
                    assignment=None,
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=res_inf,
                    primal_res_l2=res_l2,
                    integrality_gap=igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=best_violations,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=None,
                    best_candidate=best_candidate,
                    termination_reason="OVERFLOW",
                    final_x=tuple(float(xi) for xi in x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            # Rounding & deterministic verifier check
            x_floats = [float(xi) for xi in x]
            free_vals_x = {
                i: (1 if x_floats[i] >= 0.5 else 0)
                for i in range(n)
                if i not in closure.f2.pivots
            }
            for cand in (
                threshold_round(x),
                greedy_conflict_round(x, inc, ledger=ledger),
                _algebraic_guided_round(x_floats, closure, inc),
                closure.f2.evaluate_subspace_point(free_vals_x),
            ):
                ver_c = verify_assignment(instance, cand)
                if ver_c.is_sat:
                    bit_snap = ledger.end_iteration()
                    if cfg.record_iter_history:
                        iter_history.append({
                            "iteration": t,
                            "primal_res_inf": res_inf,
                            "primal_res_l2": res_l2,
                            "integrality_gap": igap,
                            "d_spec": best_d_spec,
                            **bit_snap,
                        })
                    return SolverResult(
                        status="SAT",
                        assignment=tuple(cand),
                        dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else 0.0,
                        iterations=t + 1,
                        runtime_sec=time.perf_counter() - t_start,
                        primal_res_inf=res_inf,
                        primal_res_l2=res_l2,
                        integrality_gap=igap,
                        dual_residual=last_dual_res,
                        clause_violation_count=0,
                        bit_summary=ledger.summary(),
                        iteration_history=iter_history,
                        verification=ver_c,
                        best_candidate=tuple(cand),
                        termination_reason="SAT_FOUND",
                        final_x=tuple(x_floats),
                        max_kappa2_cert_bound=kappa2_bound,
                    )
                vcount = len(ver_c.violated_clauses)
                if vcount < best_violations:
                    best_violations = vcount
                    best_candidate = tuple(cand)

            # 2. Primal-dual x-gradient
            clause_drive: list[TrackedScalar] = []
            for j in range(m):
                rj = r[j]
                beat_j = (t_sin(omega_1 * rj) / omega_1) + (t_sin(omega_2 * rj) / omega_2)
                clause_drive.append((w[j] + rho) * rj + lam[j] + gamma_beat * beat_j)

            gx_lin = ops.apply_AT(clause_drive)
            kx = ops.apply_K(x)
            g_x = [gx_lin[i] + alpha_k * kx[i] for i in range(n)]

            # 3. Fourier harmonic + Boolean pinning + Fisher-Rao pullback
            _, grad_wf = walsh_fourier_clause_eval(phi, sin_phi, sigma, w, ops)
            t_s = make_scalar(t, ledger, mode=mode, decimal_prec=dprec)
            frac_t = t_s / t_anneal_s
            if frac_t > one:
                frac_t = one
            beta_t = beta_min_s + beta_span_s * frac_t

            g_phi: list[TrackedScalar] = []
            for i in range(n):
                if fixed_mask[i] is not None:
                    g_phi.append(zero)
                else:
                    s_i = sin_phi[i]
                    pb = half * s_i * g_x[i]
                    pin = beta_t * s_i * sigma[i]
                    g_phi.append(pb + gamma_wf * grad_wf[i] + pin)

            # 4. Global Gram-preconditioned & spectrally filtered descent direction via LDL^T
            f_g = ops.apply_F_spec(g_phi, eta_spec)
            m0_inv_fg = ldlt_solve(L0_ldlt, f_g)
            g_tilde = ops.apply_F_spec(m0_inv_fg, eta_spec)

            if best_r2_norm_s is None or r2_norm_s < (best_r2_norm_s - eps_imp_s):
                best_r2_norm_s = r2_norm_s
                stall_counter = 0
            else:
                stall_counter += 1

            if stall_counter >= cfg.w_stall:
                stall_counter = 0
                raw_kick: list[TrackedScalar] = []
                three_s = ops.three
                five_s = make_scalar(5, ledger, mode=mode, decimal_prec=dprec)
                for i in range(n):
                    if fixed_mask[i] is not None:
                        raw_kick.append(zero)
                    else:
                        i_s = make_scalar(i, ledger, mode=mode, decimal_prec=dprec)
                        arg1 = (two_pi_s * i_s) / three_s + t_s * omega_1
                        arg2 = (two_pi_s * i_s) / five_s + t_s * omega_2
                        raw_kick.append(t_cos(arg1) - t_cos(arg2))
                filt_kick = ops.apply_F_spec(raw_kick, eta_spec)
                xi = [eps_kick * fk for fk in filt_kick]
            else:
                xi = [zero] * n

            # 5. Geodesic torus update & over-relaxed PDHG multiplier update
            p_next: list[TrackedScalar] = []
            phi_next: list[TrackedScalar] = []
            for i in range(n):
                fv = fixed_mask[i]
                if fv is not None:
                    p_next.append(zero)
                    phi_next.append(zero if fv == 0 else pi_s)
                else:
                    pi_new = mu_damp * p[i] - tau_step * g_tilde[i] + xi[i]
                    p_next.append(pi_new)
                    phi_next.append(t_fmod_2pi(phi[i] + pi_new, mode=mode, decimal_prec=dprec))

            if x_prev is None:
                x_bar = x
            else:
                x_bar = [x[i] + theta_pdhg * (x[i] - x_prev[i]) for i in range(n)]
            ax_bar = ops.apply_A(x_bar)
            lam_next = [
                clamp_scalar(one_minus_damp_d * lam[j] + eta_d * (ax_bar[j] - one), B_lambda)
                for j in range(m)
            ]

            dual_res_s = zero
            for i in range(n):
                dp = abs(p_next[i] - p[i])
                if dp > dual_res_s:
                    dual_res_s = dp
            for j in range(m):
                dl = abs(lam_next[j] - lam[j])
                if dl > dual_res_s:
                    dual_res_s = dl
            dual_res_val = float(dual_res_s)
            last_dual_res = dual_res_val

            p = p_next
            phi = phi_next
            x_prev = x
            lam = lam_next

            # 6. Dual spectral certificate ascent (square-root-free LDL^T)
            d_spec_float = best_d_spec
            if L_cert is not None:
                do_s_update = ((t % b_cert) == 0) and (t > 0 or b_cert == 1)
                d_spec, x_dual, b_vec, grad_y, grad_s = _evaluate_dual_certificate_ldlt(
                    y_cert, s_cert, L_cert, ops, compute_grad_s=do_s_update
                )
                d_spec_float = float(d_spec)
                if math.isfinite(d_spec_float) and d_spec_float > best_d_spec:
                    best_d_spec = d_spec_float

                x_dual_norm_sq_s = zero
                for xi_d in x_dual:
                    x_dual_norm_sq_s = x_dual_norm_sq_s + xi_d * xi_d
                eps_cert_s = eps_cert_floor_s + cert_tol_coeff_s * x_dual_norm_sq_s

                if cert_pd_verified and is_finite_scalar(d_spec) and d_spec > eps_cert_s:
                    bit_snap = ledger.end_iteration()
                    if cfg.record_iter_history:
                        iter_history.append({
                            "iteration": t,
                            "primal_res_inf": res_inf,
                            "primal_res_l2": res_l2,
                            "integrality_gap": igap,
                            "d_spec": d_spec_float,
                            **bit_snap,
                        })
                    return SolverResult(
                        status="UNSAT_CERTIFIED",
                        assignment=None,
                        dual_certificate_value=d_spec_float,
                        iterations=t + 1,
                        runtime_sec=time.perf_counter() - t_start,
                        primal_res_inf=res_inf,
                        primal_res_l2=res_l2,
                        integrality_gap=igap,
                        dual_residual=dual_res_val,
                        clause_violation_count=best_violations,
                        bit_summary=ledger.summary(),
                        iteration_history=iter_history,
                        verification=None,
                        best_candidate=best_candidate,
                        termination_reason="UNSAT_CERT",
                        final_x=tuple(x_floats),
                        max_kappa2_cert_bound=kappa2_bound,
                    )

                y_cert = [
                    clamp_scalar(y_cert[j] + alpha_y * grad_y[j], B_y)
                    for j in range(m)
                ]

                if do_s_update:
                    step_s_scalar = alpha_s_s
                    s_accepted = False
                    for _ in range(cfg.k_bt):
                        s_cand: list[TrackedScalar] = []
                        for i in range(n):
                            sc = clamp_scalar(s_cert[i] + step_s_scalar * grad_s[i], B_s_eff)
                            if inc.degrees[i] == 0 and sc < two_eps_chol:
                                sc = two_eps_chol
                            s_cand.append(sc)
                        m_shifted = build_M_cert(ops, s_cand, shift_diag=eps_chol)
                        if ldlt_factor(m_shifted, ledger, mode=mode, decimal_prec=dprec) is not None:
                            m_full = build_M_cert(ops, s_cand)
                            new_factor = ldlt_factor(m_full, ledger, mode=mode, decimal_prec=dprec)
                            if new_factor is not None:
                                s_cert = s_cand
                                L_cert = new_factor
                                cert_pd_verified = True
                                s_accepted = True
                                break
                        step_s_scalar = step_s_scalar * half

                    if not s_accepted:
                        L_sh = ldlt_factor(
                            build_M_cert(ops, s_cert, shift_diag=eps_chol),
                            ledger,
                            mode=mode,
                            decimal_prec=dprec,
                        )
                        if L_sh is not None:
                            margins = _ldlt_diag_margins(L_sh, ledger, mode=mode, decimal_prec=dprec)
                            for budget in (budget_85, budget_50):
                                s_cand = list(s_cert)
                                dec_entries: list[tuple[TrackedScalar, int, TrackedScalar]] = []
                                for i in range(n):
                                    if grad_s[i] >= zero:
                                        s_cand[i] = clamp_scalar(
                                            s_cert[i] + alpha_s_s * grad_s[i], B_s_eff
                                        )
                                    else:
                                        dec_i = -(alpha_s_s * grad_s[i])
                                        if inc.degrees[i] == 0:
                                            max_d0 = s_cert[i] - two_eps_chol
                                            if max_d0 <= zero:
                                                dec_i = zero
                                            elif dec_i > max_d0:
                                                dec_i = max_d0
                                        max_box = s_cert[i] + B_s_eff
                                        if dec_i > max_box:
                                            dec_i = max_box
                                        if dec_i > zero:
                                            dec_entries.append((dec_i / margins[i], i, dec_i))
                                dec_entries.sort(key=lambda item: item[0].value)
                                cum_ratio = zero
                                for r_i, i, dec_i in dec_entries:
                                    if cum_ratio + r_i <= budget:
                                        s_cand[i] = s_cert[i] - dec_i
                                        cum_ratio = cum_ratio + r_i
                                    else:
                                        rem = budget - cum_ratio
                                        if rem > zero:
                                            s_cand[i] = s_cert[i] - rem * margins[i]
                                        break
                                m_shifted = build_M_cert(ops, s_cand, shift_diag=eps_chol)
                                if ldlt_factor(m_shifted, ledger, mode=mode, decimal_prec=dprec) is not None:
                                    m_full = build_M_cert(ops, s_cand)
                                    new_factor = ldlt_factor(m_full, ledger, mode=mode, decimal_prec=dprec)
                                    if new_factor is not None:
                                        s_cert = s_cand
                                        L_cert = new_factor
                                        cert_pd_verified = True
                                        break

            bit_snap = ledger.end_iteration()
            if cfg.record_iter_history:
                iter_history.append({
                    "iteration": t,
                    "primal_res_inf": res_inf,
                    "primal_res_l2": res_l2,
                    "integrality_gap": igap,
                    "d_spec": d_spec_float if math.isfinite(d_spec_float) else None,
                    **bit_snap,
                })

            if ledger.nan_count > 0 or ledger.overflow_count > 0 or ledger.guardrail_tripped:
                return SolverResult(
                    status="OVERFLOW",
                    assignment=None,
                    dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=last_res_inf,
                    primal_res_l2=last_res_l2,
                    integrality_gap=last_igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=best_violations,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=None,
                    best_candidate=best_candidate,
                    termination_reason="OVERFLOW",
                    final_x=tuple(float(xi) for xi in last_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

        return SolverResult(
            status="UNRESOLVED",
            assignment=None,
            dual_certificate_value=best_d_spec if math.isfinite(best_d_spec) else -math.inf,
            iterations=max_iters,
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=last_res_inf,
            primal_res_l2=last_res_l2,
            integrality_gap=last_igap,
            dual_residual=last_dual_res,
            clause_violation_count=best_violations,
            bit_summary=ledger.summary(),
            iteration_history=iter_history,
            verification=None,
            best_candidate=best_candidate,
            termination_reason="MAX_ITERS",
            final_x=tuple(float(xi) for xi in last_x),
            max_kappa2_cert_bound=kappa2_bound,
        )

    except BitWidthExceededError:
        return SolverResult(
            status="OVERFLOW",
            assignment=None,
            dual_certificate_value=-math.inf,
            iterations=len(ledger.iteration_bit_history),
            runtime_sec=time.perf_counter() - t_start,
            primal_res_inf=math.inf,
            primal_res_l2=math.inf,
            integrality_gap=1.0,
            dual_residual=math.inf,
            clause_violation_count=m,
            bit_summary=ledger.summary(),
            iteration_history=[],
            verification=None,
            best_candidate=None,
            termination_reason="OVERFLOW",
            final_x=(),
            max_kappa2_cert_bound=(18.0 * m + b_s_eff_float) / cfg.eps_chol,
        )
