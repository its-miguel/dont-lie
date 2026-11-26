"""Track A: Sparse Degree-3 / Local Clique SoS & RLT Lift solver for Monotone 1-in-3 SAT.

Strictly isolated from generators.py, harness.py, and any external SAT/CSP/ILP solvers.
Pure Python 3.11 stdlib only. All integer and float arithmetic is instrumented via BitLedger.
Every returned SAT assignment is verified by the independent deterministic verifier.
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
    TrackedInt,
    make_scalar,
)
from ..instance import Monotone1in3Instance, SparseIncidence, build_incidence
from ..primitives import LDLTFactor, ldlt_factor, ldlt_solve
from ..solver import SolverConfig, SolverResult
from ..verifier import verify_assignment


@dataclass
class _RLTLift:
    """Result of polynomial-time sparse degree-2/3 RLT algebraic closure and clique lift."""

    unsat_proven: bool
    unsat_reason: str
    n_orig: int
    parent: list[int]
    forced: dict[int, int]  # uf_root -> 0 or 1
    active_roots: list[int]  # sorted unassigned UF roots
    root_to_idx: dict[int, int]  # uf_root -> compact index in [0, k)
    # Compact-index constraints on [0, k)
    eq_clauses: list[tuple[int, ...]]  # each tuple sums to 1 (len 2 or 3)
    cliques: list[tuple[int, ...]]  # each tuple sums to <= 1 (len >= 3)
    implications: list[tuple[int, int]]  # (d, c) meaning x_d <= x_c
    adj_compact: list[list[int]]  # conflict adjacency on [0, k)
    # Telemetry
    num_equivalences: int
    num_forced: int
    num_implications: int
    num_cliques: int


def _uf_find(parent: list[int], x: int) -> int:
    while parent[x] != x:
        parent[x] = parent[parent[x]]
        x = parent[x]
    return x


def _build_rlt_lift(
    instance: Monotone1in3Instance,
    inc: SparseIncidence,
    ledger: BitLedger,
) -> _RLTLift:
    """Perform polynomial-time sparse degree-2/3 RLT closure and conflict-clique extraction.

    Every deduction is an exact low-degree polynomial identity in the Monotone 1-in-3 SAT ideal:
      - Clause equalities: x_a + x_b + x_c = 1, pairwise x_u * x_v = 0
      - Repeated literals: 2*x_a + x_b = 1 => x_a = 0, x_b = 1; 3*x_a = 1 => UNSAT
      - Shared-2 overlapping clauses: (a,b,c) & (a,b,d) => x_c = x_d
      - Self-conflict equivalence: x_u = x_v and x_u*x_v = 0 => x_u = x_v = 0
      - Degree-2 RLT 1-var overlap: x_d = x_d*(x_a+x_b+x_c) =>
          * if d conflicts with a,b,c: x_d = 0
          * if d conflicts with a,b: x_d <= x_c
      - Degree-3 RLT collapse:
          * if x_d <= x_c1, x_d <= x_c2, and (c1,c2) in E_K: x_d = x_d*(x_c1*x_c2) = 0
          * if x_d <= x_c and x_c <= x_d: x_d = x_c
          * if x_d <= x_c and (d,c) in E_K: x_d = 0
    """
    n = instance.n_vars
    m = instance.m_clauses

    # Record degree and incidence integers in BitLedger
    for d in inc.degrees:
        ledger.record_int(d, count_op=False)
    ledger.record_int(n, count_op=False)
    ledger.record_int(m, count_op=False)

    parent = list(range(n))
    forced: dict[int, int] = {}
    adj: list[set[int]] = [set() for _ in range(n)]
    imp_out: list[set[int]] = [set() for _ in range(n)]
    imp_in: list[set[int]] = [set() for _ in range(n)]
    comp_pairs: set[tuple[int, int]] = set()
    num_equiv = 0

    def empty_unsat(reason: str) -> _RLTLift:
        return _RLTLift(
            unsat_proven=True,
            unsat_reason=reason,
            n_orig=n,
            parent=parent,
            forced=forced,
            active_roots=[],
            root_to_idx={},
            eq_clauses=[],
            cliques=[],
            implications=[],
            adj_compact=[],
            num_equivalences=num_equiv,
            num_forced=len(forced),
            num_implications=0,
            num_cliques=0,
        )

    def force_val(u: int, val: int) -> bool:
        r = _uf_find(parent, u)
        prev = forced.get(r)
        if prev is not None:
            return prev == val
        forced[r] = val
        ledger.record_int(val, count_op=True)
        return True

    def union_vars(u: int, v: int) -> bool:
        nonlocal num_equiv
        ru = _uf_find(parent, u)
        rv = _uf_find(parent, v)
        if ru == rv:
            return True
        if ru > rv:
            ru, rv = rv, ru
        fu = forced.get(ru)
        fv = forced.get(rv)
        if fu is not None and fv is not None and fu != fv:
            return False
        parent[rv] = ru
        num_equiv += 1
        ledger.record_int(num_equiv, count_op=True)
        if fu is None and fv is not None:
            forced[ru] = fv
        if rv in forced:
            del forced[rv]
        # Merge adjacency
        adj[ru].update(adj[rv])
        adj[rv].clear()
        # Merge implications
        imp_out[ru].update(imp_out[rv])
        imp_out[rv].clear()
        imp_in[ru].update(imp_in[rv])
        imp_in[rv].clear()
        return True

    # Initialize conflict graph from raw clauses
    for a, b, c in instance.clauses:
        if a != b:
            adj[a].add(b)
            adj[b].add(a)
        if b != c:
            adj[b].add(c)
            adj[c].add(b)
        if a != c:
            adj[a].add(c)
            adj[c].add(a)

    # Fixed-point polynomial RLT closure
    max_passes = min(40, max(12, n))
    for _pass in range(max_passes):
        changed = False
        prev_forced_cnt = len(forced)
        prev_equiv_cnt = num_equiv
        prev_imp_cnt = sum(len(s) for s in imp_out)
        prev_comp_cnt = len(comp_pairs)

        # (a) Clause unit, multiplicity, and complement propagation
        active_3clauses: list[tuple[int, int, int]] = []
        new_comp_pairs: set[tuple[int, int]] = set()
        for a, b, c in instance.clauses:
            ra = _uf_find(parent, a)
            rb = _uf_find(parent, b)
            rc = _uf_find(parent, c)

            # Handle repeated representatives in the same clause
            if ra == rb and rb == rc:
                return empty_unsat("RLT_3X_EQ_1_CONTRADICTION")
            if ra == rb:
                if not force_val(ra, 0) or not force_val(rc, 1):
                    return empty_unsat("RLT_2X_PLUS_Y_CONTRADICTION")
                continue
            if ra == rc:
                if not force_val(ra, 0) or not force_val(rb, 1):
                    return empty_unsat("RLT_2X_PLUS_Y_CONTRADICTION")
                continue
            if rb == rc:
                if not force_val(rb, 0) or not force_val(ra, 1):
                    return empty_unsat("RLT_2X_PLUS_Y_CONTRADICTION")
                continue

            ones = 0
            zeros = 0
            unassigned: list[int] = []
            for r in (ra, rb, rc):
                fv = forced.get(r)
                if fv == 1:
                    ones += 1
                elif fv == 0:
                    zeros += 1
                else:
                    unassigned.append(r)

            if ones > 1:
                return empty_unsat("RLT_CLAUSE_SUM_GT_1")
            if ones == 1:
                for r in unassigned:
                    if not force_val(r, 0):
                        return empty_unsat("RLT_UNIT_ZERO_CONFLICT")
            else:
                if zeros == 3:
                    return empty_unsat("RLT_CLAUSE_ALL_ZERO")
                if len(unassigned) == 1:
                    if not force_val(unassigned[0], 1):
                        return empty_unsat("RLT_UNIT_ONE_CONFLICT")
                elif len(unassigned) == 2:
                    u0, u1 = unassigned[0], unassigned[1]
                    if u0 > u1:
                        u0, u1 = u1, u0
                    new_comp_pairs.add((u0, u1))
                    adj[u0].add(u1)
                    adj[u1].add(u0)
                else:
                    s0, s1, s2 = sorted(unassigned)
                    active_3clauses.append((s0, s1, s2))

        # Re-normalize existing comp_pairs
        for u, v in comp_pairs:
            ru = _uf_find(parent, u)
            rv = _uf_find(parent, v)
            if ru == rv:
                return empty_unsat("RLT_COMP_PAIR_EQUAL_CONTRADICTION")
            fu = forced.get(ru)
            fv = forced.get(rv)
            if fu is not None and fv is not None:
                if fu + fv != 1:
                    return empty_unsat("RLT_COMP_PAIR_SUM_CONTRADICTION")
                continue
            if fu is not None:
                if not force_val(rv, 1 - fu):
                    return empty_unsat("RLT_COMP_PAIR_PROP_CONFLICT")
                continue
            if fv is not None:
                if not force_val(ru, 1 - fv):
                    return empty_unsat("RLT_COMP_PAIR_PROP_CONFLICT")
                continue
            if ru > rv:
                ru, rv = rv, ru
            new_comp_pairs.add((ru, rv))
            adj[ru].add(rv)
            adj[rv].add(ru)
        comp_pairs = new_comp_pairs

        # (b) Shared-2 overlapping clause equivalences: (a,b,c) & (a,b,d) => x_c = x_d
        pair_to_third: dict[tuple[int, int], int] = {}
        for s0, s1, s2 in active_3clauses:
            for p_key, third in (((s0, s1), s2), ((s0, s2), s1), ((s1, s2), s0)):
                prev_third = pair_to_third.get(p_key)
                if prev_third is None:
                    pair_to_third[p_key] = third
                elif _uf_find(parent, prev_third) != _uf_find(parent, third):
                    if not union_vars(prev_third, third):
                        return empty_unsat("RLT_SHARED2_EQUIV_CONTRADICTION")

        # Complement-pair shared-1 equivalences: (u+v=1) & (u+w=1) => v = w
        comp_partner: dict[int, int] = {}
        for u, v in comp_pairs:
            ru = _uf_find(parent, u)
            rv = _uf_find(parent, v)
            if ru == rv:
                return empty_unsat("RLT_COMP_SELF_CONTRADICTION")
            pu = comp_partner.get(ru)
            if pu is None:
                comp_partner[ru] = rv
            elif _uf_find(parent, pu) != rv:
                if not union_vars(pu, rv):
                    return empty_unsat("RLT_COMP_EQUIV_CONTRADICTION")
            pv = comp_partner.get(rv)
            if pv is None:
                comp_partner[rv] = ru
            elif _uf_find(parent, pv) != ru:
                if not union_vars(pv, ru):
                    return empty_unsat("RLT_COMP_EQUIV_CONTRADICTION")

        # (c) Re-project conflict graph onto current UF roots & check self-conflicts
        roots_present = sorted({_uf_find(parent, i) for i in range(n)})
        for r in roots_present:
            if adj[r]:
                new_nb: set[int] = set()
                for nb in adj[r]:
                    rnb = _uf_find(parent, nb)
                    new_nb.add(rnb)
                adj[r] = new_nb
            if r in adj[r]:
                # x_r = x_r^2 = 0
                if not force_val(r, 0):
                    return empty_unsat("RLT_SELF_CONFLICT_EQUIV_CONTRADICTION")
            if forced.get(r) == 1:
                for nb in adj[r]:
                    if not force_val(nb, 0):
                        return empty_unsat("RLT_CONFLICT_NEIGHBOR_ONE_CONTRADICTION")

        # Symmetrize quotient adjacency
        for r in roots_present:
            for nb in list(adj[r]):
                if nb != r:
                    adj[nb].add(r)

        # (d) Degree-2 RLT 1-variable-overlap / clause-neighbor implications:
        #     x_d = x_d*(x_a + x_b + x_c) = x_a*x_d + x_b*x_d + x_c*x_d
        for s0, s1, s2 in active_3clauses:
            ra = _uf_find(parent, s0)
            rb = _uf_find(parent, s1)
            rc = _uf_find(parent, s2)
            if ra in forced or rb in forced or rc in forced:
                continue
            if ra == rb or ra == rc or rb == rc:
                continue
            nb_a = adj[ra]
            nb_b = adj[rb]
            nb_c = adj[rc]
            c_ab = nb_a & nb_b
            c_ac = nb_a & nb_c
            c_bc = nb_b & nb_c
            all3 = c_ab & nb_c
            for d in all3:
                if not force_val(d, 0):
                    return empty_unsat("RLT_DEG2_ALL3_CONFLICT_CONTRADICTION")
            for pair_set, target in ((c_ab, rc), (c_ac, rb), (c_bc, ra)):
                for d in pair_set:
                    if d in all3 or d == target or d in forced:
                        continue
                    if target in adj[d]:
                        if not force_val(d, 0):
                            return empty_unsat("RLT_DEG2_IMP_CONFLICT_CONTRADICTION")
                    else:
                        imp_out[d].add(target)
                        imp_in[target].add(d)
                        if d in imp_out[target]:
                            if not union_vars(d, target):
                                return empty_unsat("RLT_MUTUAL_IMP_EQUIV_CONTRADICTION")

        # Complement-pair degree-2 RLT annihilator: x_d = x_d*(x_u + x_v) = 0 if d in adj[u] & adj[v]
        for u, v in comp_pairs:
            ru = _uf_find(parent, u)
            rv = _uf_find(parent, v)
            if ru in forced or rv in forced:
                continue
            for d in adj[ru] & adj[rv]:
                if not force_val(d, 0):
                    return empty_unsat("RLT_COMP_PAIR_ANNIHILATOR_CONTRADICTION")

        # (e) Degree-3 RLT implication-conflict & 1-hop transitivity collapse
        for r in roots_present:
            if not imp_out[r]:
                continue
            # Re-normalize imp_out[r]
            norm_out: set[int] = set()
            for c in imp_out[r]:
                rc = _uf_find(parent, c)
                if rc != r:
                    norm_out.add(rc)
            imp_out[r] = norm_out
            if r in forced:
                if forced[r] == 1:
                    for rc in norm_out:
                        if not force_val(rc, 1):
                            return empty_unsat("RLT_IMP_FORCED1_CONTRADICTION")
                continue

            out_list = sorted(norm_out)
            killed_r = False
            for idx_i, c1 in enumerate(out_list):
                if forced.get(c1) == 0 or c1 in adj[r]:
                    if not force_val(r, 0):
                        return empty_unsat("RLT_IMP_ZERO_OR_SELF_CONTRADICTION")
                    killed_r = True
                    break
                if r in imp_out[c1]:
                    if not union_vars(r, c1):
                        return empty_unsat("RLT_IMP_CYCLE_CONTRADICTION")
                # Degree-3 identity: x_r <= x_c1, x_r <= x_c2, (c1,c2) in E_K => x_r = 0
                nb_c1 = adj[c1]
                for c2 in out_list[idx_i + 1 :]:
                    if c2 in nb_c1:
                        if not force_val(r, 0):
                            return empty_unsat("RLT_DEG3_IMP_CONFLICT_CONTRADICTION")
                        killed_r = True
                        break
                if killed_r:
                    break
                # 1-hop transitivity check
                for f in imp_out[c1]:
                    rf = _uf_find(parent, f)
                    if forced.get(rf) == 0 or rf in adj[r] or rf in adj[c1]:
                        if not force_val(r, 0):
                            return empty_unsat("RLT_DEG3_TRANS_CONFLICT_CONTRADICTION")
                        killed_r = True
                        break
                if killed_r:
                    break

        new_imp_cnt = sum(len(s) for s in imp_out)
        if (
            len(forced) > prev_forced_cnt
            or num_equiv > prev_equiv_cnt
            or new_imp_cnt > prev_imp_cnt
            or len(comp_pairs) > prev_comp_cnt
        ):
            changed = True
        if not changed:
            break

    # Final verification of all clauses against forced values (in case last pass forced variables)
    active_roots_set: set[int] = set()
    for i in range(n):
        r = _uf_find(parent, i)
        if r not in forced:
            active_roots_set.add(r)
    active_roots = sorted(active_roots_set)
    root_to_idx = {r: idx for idx, r in enumerate(active_roots)}
    k = len(active_roots)

    eq_set: set[tuple[int, ...]] = set()
    for a, b, c in instance.clauses:
        ra = _uf_find(parent, a)
        rb = _uf_find(parent, b)
        rc = _uf_find(parent, c)
        ones = 0
        rem: list[int] = []
        for r in (ra, rb, rc):
            fv = forced.get(r)
            if fv == 1:
                ones += 1
            elif fv is None:
                rem.append(r)
        if ones > 1:
            return empty_unsat("RLT_FINAL_CLAUSE_SUM_GT_1")
        if ones == 1:
            if rem:
                return empty_unsat("RLT_FINAL_UNPROP_ZERO")
            continue
        if not rem:
            return empty_unsat("RLT_FINAL_CLAUSE_ALL_ZERO")
        if len(rem) == 1:
            # Should have been forced to 1
            if not force_val(rem[0], 1):
                return empty_unsat("RLT_FINAL_UNIT_CONFLICT")
            continue
        if len(set(rem)) < len(rem):
            return empty_unsat("RLT_FINAL_DUP_ACTIVE")
        eq_set.add(tuple(sorted(root_to_idx[r] for r in rem)))

    for u, v in comp_pairs:
        ru = _uf_find(parent, u)
        rv = _uf_find(parent, v)
        fu = forced.get(ru)
        fv = forced.get(rv)
        if fu is not None and fv is not None:
            if fu + fv != 1:
                return empty_unsat("RLT_FINAL_COMP_CONTRADICTION")
            continue
        if ru in root_to_idx and rv in root_to_idx:
            i0, i1 = root_to_idx[ru], root_to_idx[rv]
            if i0 > i1:
                i0, i1 = i1, i0
            eq_set.add((i0, i1))

    eq_clauses = sorted(eq_set)

    # Compact conflict adjacency on [0, k)
    adj_sets_c: list[set[int]] = [set() for _ in range(k)]
    for r, idx in root_to_idx.items():
        for nb in adj[r]:
            nb_r = _uf_find(parent, nb)
            nb_idx = root_to_idx.get(nb_r)
            if nb_idx is not None and nb_idx != idx:
                adj_sets_c[idx].add(nb_idx)
                adj_sets_c[nb_idx].add(idx)
    adj_compact = [sorted(s) for s in adj_sets_c]

    # Compact implications on [0, k)
    imp_set: set[tuple[int, int]] = set()
    for r, idx in root_to_idx.items():
        for c in imp_out[r]:
            rc = _uf_find(parent, c)
            c_idx = root_to_idx.get(rc)
            if c_idx is not None and c_idx != idx:
                imp_set.add((idx, c_idx))
    implications = sorted(imp_set)

    # Extract maximal cliques of size >= 3 from compact conflict graph
    clique_set: set[tuple[int, ...]] = set()
    max_cliques = max(3 * m, 150)
    for u in range(k):
        nb_u = adj_sets_c[u]
        if len(nb_u) < 2:
            continue
        for v in adj_compact[u]:
            if v <= u:
                continue
            common = nb_u & adj_sets_c[v]
            if not common:
                continue
            clq = [u, v]
            while common:
                best_w = -1
                best_deg = -1
                for w in sorted(common):
                    deg = len(adj_sets_c[w] & common)
                    if deg > best_deg:
                        best_deg = deg
                        best_w = w
                if best_w == -1:
                    break
                clq.append(best_w)
                common = common & adj_sets_c[best_w]
            if len(clq) >= 3:
                clq_t = tuple(sorted(clq))
                if clq_t not in eq_set:
                    clique_set.add(clq_t)
                    ledger.record_int(len(clq_t), count_op=True)
            if len(clique_set) >= max_cliques * 2:
                break
        if len(clique_set) >= max_cliques * 2:
            break

    cliques = sorted(clique_set, key=lambda c: (-len(c), c))[:max_cliques]

    return _RLTLift(
        unsat_proven=False,
        unsat_reason="",
        n_orig=n,
        parent=parent,
        forced=forced,
        active_roots=active_roots,
        root_to_idx=root_to_idx,
        eq_clauses=eq_clauses,
        cliques=cliques,
        implications=implications,
        adj_compact=adj_compact,
        num_equivalences=num_equiv,
        num_forced=len(forced),
        num_implications=len(implications),
        num_cliques=len(cliques),
    )


def _rlt1_lift_closure(
    instance: Monotone1in3Instance,
    inc: SparseIncidence,
    lift: _RLTLift,
    ledger: BitLedger,
) -> _RLTLift:
    """Polynomial-time Level-1 RLT lift-and-project closure (non-recursive, O(k^2 * m)).

    For each unassigned variable v, multiplies the active linear/conflict system by x_v
    and by (1 - x_v) via single-level unit/conflict propagation:
      - x_v * (system) -> 0=1  =>  x_v = 0
      - (1 - x_v) * (system) -> 0=1  =>  x_v = 1
      - both -> 0=1  =>  exact RLT-1 UNSAT proof
      - x_v=1 => x_u=b AND x_v=0 => x_u=b  =>  x_u = x_v*x_u + (1-x_v)*x_u = b
      - x_v=1 => x_u=0  =>  derived conflict edge x_v * x_u = 0
      - x_v=1 => x_u=1  =>  derived RLT implication x_v <= x_u
    """
    k = len(lift.active_roots)
    if lift.unsat_proven or k == 0:
        return lift

    eq_clauses = lift.eq_clauses
    adj_sets = [set(nbs) for nbs in lift.adj_compact]
    imp_out = [set() for _ in range(k)]
    for d, c in lift.implications:
        imp_out[d].add(c)

    var_clauses: list[list[int]] = [[] for _ in range(k)]
    for ci, cl in enumerate(eq_clauses):
        for v in cl:
            var_clauses[v].append(ci)

    g_forced: list[int | None] = [None] * k

    def prop_branch(init_var: int, init_val: int) -> list[int | None] | None:
        a = list(g_forced)
        if a[init_var] is not None:
            if a[init_var] != init_val:
                return None
            return a
        a[init_var] = init_val
        q: deque[int] = deque([init_var])
        while q:
            u = q.popleft()
            vu = a[u]
            if vu == 1:
                for nb in adj_sets[u]:
                    av = a[nb]
                    if av == 1:
                        return None
                    if av is None:
                        a[nb] = 0
                        q.append(nb)
                for tgt in imp_out[u]:
                    av = a[tgt]
                    if av == 0:
                        return None
                    if av is None:
                        a[tgt] = 1
                        q.append(tgt)
            for ci in var_clauses[u]:
                cl = eq_clauses[ci]
                ones = 0
                unass0 = -1
                unass_cnt = 0
                for v in cl:
                    av = a[v]
                    if av == 1:
                        ones += 1
                    elif av is None:
                        unass0 = v
                        unass_cnt += 1
                if ones > 1:
                    return None
                if ones == 1:
                    if unass_cnt > 0:
                        for v in cl:
                            if a[v] is None:
                                a[v] = 0
                                q.append(v)
                else:
                    if unass_cnt == 0:
                        return None
                    if unass_cnt == 1:
                        a[unass0] = 1
                        q.append(unass0)
        return a

    def force_global(u: int, val: int) -> bool:
        if g_forced[u] is not None:
            return g_forced[u] == val
        res = prop_branch(u, val)
        if res is None:
            return False
        for i in range(k):
            if res[i] is not None:
                if g_forced[i] is not None and g_forced[i] != res[i]:
                    return False
                g_forced[i] = res[i]
        ledger.record_int(val, count_op=True)
        return True

    max_rounds = min(10, max(3, k))
    any_new_facts = False
    for _round in range(max_rounds):
        round_changed = False
        for v in range(k):
            if g_forced[v] is not None:
                continue
            r1 = prop_branch(v, 1)
            r0 = prop_branch(v, 0)
            if r1 is None and r0 is None:
                return _RLTLift(
                    unsat_proven=True,
                    unsat_reason="RLT1_LIFT_PROJECTION_UNSAT",
                    n_orig=lift.n_orig,
                    parent=lift.parent,
                    forced=lift.forced,
                    active_roots=[],
                    root_to_idx={},
                    eq_clauses=[],
                    cliques=[],
                    implications=[],
                    adj_compact=[],
                    num_equivalences=lift.num_equivalences,
                    num_forced=lift.num_forced,
                    num_implications=lift.num_implications,
                    num_cliques=lift.num_cliques,
                )
            if r1 is None:
                if not force_global(v, 0):
                    return _RLTLift(
                        unsat_proven=True,
                        unsat_reason="RLT1_FORCE0_UNSAT",
                        n_orig=lift.n_orig,
                        parent=lift.parent,
                        forced=lift.forced,
                        active_roots=[],
                        root_to_idx={},
                        eq_clauses=[],
                        cliques=[],
                        implications=[],
                        adj_compact=[],
                        num_equivalences=lift.num_equivalences,
                        num_forced=lift.num_forced,
                        num_implications=lift.num_implications,
                        num_cliques=lift.num_cliques,
                    )
                round_changed = True
                any_new_facts = True
                continue
            if r0 is None:
                if not force_global(v, 1):
                    return _RLTLift(
                        unsat_proven=True,
                        unsat_reason="RLT1_FORCE1_UNSAT",
                        n_orig=lift.n_orig,
                        parent=lift.parent,
                        forced=lift.forced,
                        active_roots=[],
                        root_to_idx={},
                        eq_clauses=[],
                        cliques=[],
                        implications=[],
                        adj_compact=[],
                        num_equivalences=lift.num_equivalences,
                        num_forced=lift.num_forced,
                        num_implications=lift.num_implications,
                        num_cliques=lift.num_cliques,
                    )
                round_changed = True
                any_new_facts = True
                continue

            # Both branches consistent: extract unconditional consequences & RLT-1 cuts
            for u in range(k):
                if g_forced[u] is not None:
                    continue
                v1 = r1[u]
                v0 = r0[u]
                if v1 is not None and v1 == v0:
                    if not force_global(u, v1):
                        return _RLTLift(
                            unsat_proven=True,
                            unsat_reason="RLT1_BACKBONE_UNSAT",
                            n_orig=lift.n_orig,
                            parent=lift.parent,
                            forced=lift.forced,
                            active_roots=[],
                            root_to_idx={},
                            eq_clauses=[],
                            cliques=[],
                            implications=[],
                            adj_compact=[],
                            num_equivalences=lift.num_equivalences,
                            num_forced=lift.num_forced,
                            num_implications=lift.num_implications,
                            num_cliques=lift.num_cliques,
                        )
                    round_changed = True
                    any_new_facts = True
                elif u != v and v1 == 0 and u not in adj_sets[v]:
                    adj_sets[v].add(u)
                    adj_sets[u].add(v)
                    any_new_facts = True
                elif u != v and v1 == 1 and u not in imp_out[v]:
                    imp_out[v].add(u)
                    any_new_facts = True
        if not round_changed:
            break

    if not any_new_facts:
        return lift

    # Rebuild compact lift with newly forced values, conflicts, and implications
    new_forced = dict(lift.forced)
    for idx, fv in enumerate(g_forced):
        if fv is not None:
            new_forced[lift.active_roots[idx]] = fv

    new_active_roots = [r for idx, r in enumerate(lift.active_roots) if g_forced[idx] is None]
    new_root_to_idx = {r: i for i, r in enumerate(new_active_roots)}
    old_to_new = {
        old_idx: new_root_to_idx[lift.active_roots[old_idx]]
        for old_idx in range(k)
        if g_forced[old_idx] is None
    }
    k_new = len(new_active_roots)

    new_eq_set: set[tuple[int, ...]] = set()
    for cl in eq_clauses:
        ones = 0
        rem: list[int] = []
        for old_v in cl:
            fv = g_forced[old_v]
            if fv == 1:
                ones += 1
            elif fv is None:
                rem.append(old_to_new[old_v])
        if ones > 1 or (ones == 0 and len(rem) == 0):
            return _RLTLift(
                unsat_proven=True,
                unsat_reason="RLT1_REBUILD_UNSAT",
                n_orig=lift.n_orig,
                parent=lift.parent,
                forced=new_forced,
                active_roots=[],
                root_to_idx={},
                eq_clauses=[],
                cliques=[],
                implications=[],
                adj_compact=[],
                num_equivalences=lift.num_equivalences,
                num_forced=len(new_forced),
                num_implications=0,
                num_cliques=0,
            )
        if ones == 0 and len(rem) >= 2:
            new_eq_set.add(tuple(sorted(rem)))

    new_adj_sets: list[set[int]] = [set() for _ in range(k_new)]
    for old_u, new_u in old_to_new.items():
        for old_v in adj_sets[old_u]:
            new_v = old_to_new.get(old_v)
            if new_v is not None and new_v != new_u:
                new_adj_sets[new_u].add(new_v)
                new_adj_sets[new_v].add(new_u)
    new_adj_compact = [sorted(s) for s in new_adj_sets]

    new_imp_set: set[tuple[int, int]] = set()
    for old_u, new_u in old_to_new.items():
        for old_c in imp_out[old_u]:
            new_c = old_to_new.get(old_c)
            if new_c is not None and new_c != new_u:
                new_imp_set.add((new_u, new_c))

    # Extract maximal cliques on updated conflict graph
    clique_set: set[tuple[int, ...]] = set()
    max_cliques = max(3 * instance.m_clauses, 150)
    for u in range(k_new):
        nb_u = new_adj_sets[u]
        if len(nb_u) < 2:
            continue
        for v in new_adj_compact[u]:
            if v <= u:
                continue
            common = nb_u & new_adj_sets[v]
            if not common:
                continue
            clq = [u, v]
            while common:
                best_w = -1
                best_deg = -1
                for w in sorted(common):
                    deg = len(new_adj_sets[w] & common)
                    if deg > best_deg:
                        best_deg = deg
                        best_w = w
                if best_w == -1:
                    break
                clq.append(best_w)
                common = common & new_adj_sets[best_w]
            if len(clq) >= 3:
                clq_t = tuple(sorted(clq))
                if clq_t not in new_eq_set:
                    clique_set.add(clq_t)
                    ledger.record_int(len(clq_t), count_op=True)
            if len(clique_set) >= max_cliques * 2:
                break
        if len(clique_set) >= max_cliques * 2:
            break

    new_cliques = sorted(clique_set, key=lambda c: (-len(c), c))[:max_cliques]
    return _RLTLift(
        unsat_proven=False,
        unsat_reason="",
        n_orig=lift.n_orig,
        parent=lift.parent,
        forced=new_forced,
        active_roots=new_active_roots,
        root_to_idx=new_root_to_idx,
        eq_clauses=sorted(new_eq_set),
        cliques=new_cliques,
        implications=sorted(new_imp_set),
        adj_compact=new_adj_compact,
        num_equivalences=lift.num_equivalences,
        num_forced=len(new_forced),
        num_implications=len(new_imp_set),
        num_cliques=len(new_cliques),
    )


def _exact_int_farkas_check(
    k: int,
    eq_clauses: Sequence[tuple[int, ...]],
    cliques: Sequence[tuple[int, ...]],
    implications: Sequence[tuple[int, int]],
    y: Sequence[float],
    mu: Sequence[float],
    nu: Sequence[float],
    ledger: BitLedger,
) -> float | None:
    """Verify a Farkas RLT+Clique UNSAT dual certificate in exact integer arithmetic.

    For any feasible x in {0,1}^k satisfying:
      - sum_{i in E_j} x_i = 1       (multipliers Y_j in Z)
      - sum_{i in C_q} x_i <= 1      (multipliers M_q in Z_{>= 0})
      - x_d - x_c <= 0               (multipliers N_r in Z_{>= 0})
    we have:
      sum_{i=0}^{k-1} min(0, C_i) <= C^T x <= sum_j Y_j + sum_q M_q.
    Therefore D_int = sum_i min(0, C_i) - sum_j Y_j - sum_q M_q > 0 is an
    exact, zero-rounding-error proof of UNSAT.
    """
    scale = 1 << 20  # 1_048_576
    cap = 1 << 30
    ledger.record_int(scale, count_op=False)

    C = [0] * k
    rhs_sum = 0

    for j, cl in enumerate(eq_clauses):
        yj = int(round(y[j] * scale))
        if yj > cap:
            yj = cap
        elif yj < -cap:
            yj = -cap
        if yj == 0:
            continue
        ledger.record_int(yj, count_op=True)
        rhs_sum += yj
        for i in cl:
            C[i] += yj

    for q, clq in enumerate(cliques):
        mq = int(round(mu[q] * scale))
        if mq <= 0:
            continue
        if mq > cap:
            mq = cap
        ledger.record_int(mq, count_op=True)
        rhs_sum += mq
        for i in clq:
            C[i] += mq

    for r, (d, c) in enumerate(implications):
        nr = int(round(nu[r] * scale))
        if nr <= 0:
            continue
        if nr > cap:
            nr = cap
        ledger.record_int(nr, count_op=True)
        C[d] += nr
        C[c] -= nr

    lhs_min = 0
    for ci in C:
        ledger.record_int(ci, count_op=True)
        if ci < 0:
            lhs_min += ci

    d_int = lhs_min - rhs_sum
    ledger.record_int(d_int, count_op=True)
    if d_int > 0:
        cert_val = float(d_int) / float(scale)
        ledger.record_float(cert_val, count_op=True)
        return cert_val
    return None


def _run_rlt_farkas_dual(
    lift: _RLTLift,
    ledger: BitLedger,
    max_dual_iters: int,
) -> tuple[bool, float, int]:
    """Run smoothed entropic / AdaGrad dual ascent on the RLT + Clique LP relaxation.

    Returns (certified_unsat, best_dual_value, iters_used).
    """
    k = len(lift.active_roots)
    m_eq = len(lift.eq_clauses)
    m_clq = len(lift.cliques)
    m_imp = len(lift.implications)
    if k == 0 or m_eq == 0:
        return False, 0.0, 0

    y = [0.0] * m_eq
    mu = [0.0] * m_clq
    nu = [0.0] * m_imp
    g2_y = [1.0] * m_eq
    g2_mu = [1.0] * m_clq
    g2_nu = [1.0] * m_imp

    best_d = -math.inf
    bound_dual = 50.0

    for it in range(max_dual_iters):
        # Compute reduced costs c = A^T y + B_clq^T mu + B_imp^T nu
        c = [0.0] * k
        rhs = 0.0
        for j, cl in enumerate(lift.eq_clauses):
            yj = y[j]
            if yj != 0.0:
                rhs += yj
                for i in cl:
                    c[i] += yj
        for q, clq in enumerate(lift.cliques):
            mq = mu[q]
            if mq > 0.0:
                rhs += mq
                for i in clq:
                    c[i] += mq
        for r, (d, t) in enumerate(lift.implications):
            nr = nu[r]
            if nr > 0.0:
                c[d] += nr
                c[t] -= nr

        # Exact piecewise-linear dual value D = sum_i min(0, c_i) - rhs
        lhs = 0.0
        for ci in c:
            if ci < 0.0:
                lhs += ci
        d_val = lhs - rhs
        ledger.record_float(d_val, count_op=True)
        if math.isfinite(d_val) and d_val > best_d:
            best_d = d_val

        if d_val > 1e-4:
            exact_cert = _exact_int_farkas_check(
                k, lift.eq_clauses, lift.cliques, lift.implications, y, mu, nu, ledger
            )
            if exact_cert is not None:
                return True, exact_cert, it + 1

        # Smoothed entropic best-response g_i = 1 / (1 + exp(beta * c_i))
        beta = 4.0 + 16.0 * (it / max(1, max_dual_iters - 1))
        g = [0.0] * k
        for i in range(k):
            z = beta * c[i]
            if z > 30.0:
                gi = 0.0
            elif z < -30.0:
                gi = 1.0
            else:
                gi = 1.0 / (1.0 + math.exp(z))
            g[i] = gi

        step = 0.6 / math.sqrt(1.0 + 0.05 * it)
        ledger.record_float(step, count_op=True)

        for j, cl in enumerate(lift.eq_clauses):
            grad = -1.0
            for i in cl:
                grad += g[i]
            g2_y[j] += grad * grad
            yv = y[j] + step * grad / math.sqrt(g2_y[j])
            if yv > bound_dual:
                yv = bound_dual
            elif yv < -bound_dual:
                yv = -bound_dual
            y[j] = yv

        for q, clq in enumerate(lift.cliques):
            grad = -1.0
            for i in clq:
                grad += g[i]
            g2_mu[q] += grad * grad
            mv = mu[q] + step * grad / math.sqrt(g2_mu[q])
            if mv < 0.0:
                mv = 0.0
            elif mv > bound_dual:
                mv = bound_dual
            mu[q] = mv

        for r, (d, t) in enumerate(lift.implications):
            grad = g[d] - g[t]
            g2_nu[r] += grad * grad
            nv = nu[r] + step * grad / math.sqrt(g2_nu[r])
            if nv < 0.0:
                nv = 0.0
            elif nv > bound_dual:
                nv = bound_dual
            nu[r] = nv

    # Final exact integer check if best_d is positive
    if best_d > 1e-6:
        exact_cert = _exact_int_farkas_check(
            k, lift.eq_clauses, lift.cliques, lift.implications, y, mu, nu, ledger
        )
        if exact_cert is not None:
            return True, exact_cert, max_dual_iters

    return False, (best_d if math.isfinite(best_d) else -math.inf), max_dual_iters


def _run_ldlt_spectral_dual(
    inc: SparseIncidence,
    ledger: BitLedger,
    cfg: SolverConfig,
    max_steps: int,
) -> tuple[bool, float, float]:
    """Run square-root-free LDL^T spectral dual certificate ascent from primitives.py.

    Uses ldlt_factor and ldlt_solve directly (no square roots, no Fraction Cholesky blowup).
    Returns (certified_unsat, best_d_spec, kappa2_bound).
    """
    n = inc.n_vars
    m = inc.m_clauses
    eps_chol = cfg.eps_chol
    b_s_eff = max(cfg.B_s, float(inc.max_degree) + 2.0 * eps_chol + 1.0)
    kappa2_bound = (18.0 * m + b_s_eff) / eps_chol

    if n == 0 or m == 0 or max_steps <= 0:
        return False, -math.inf, kappa2_bound

    # Build exact integer A^T A and record in BitLedger
    ata = inc.compute_ata_matrix()
    for i in range(n):
        row = ata[i]
        for j in range(n):
            if row[j] != 0:
                ledger.record_int(row[j], count_op=False)

    # Initial s_cert = d + 2*eps_chol*1 (guaranteed M_cert - eps_chol*I >= 2 A^T A + eps_chol*I > 0)
    mode = "float64" if cfg.mode == "fraction" else cfg.mode
    dprec = cfg.decimal_prec
    s_vals = [min(b_s_eff, float(inc.degrees[i]) + 2.0 * eps_chol) for i in range(n)]

    mat_shifted = [
        [
            make_scalar(
                float(2 * ata[i][j])
                + (s_vals[i] - float(inc.degrees[i]) - eps_chol if i == j else 0.0),
                ledger,
                mode=mode,
                decimal_prec=dprec,
            )
            for j in range(n)
        ]
        for i in range(n)
    ]
    fac_shifted = ldlt_factor(mat_shifted, ledger, mode=mode, decimal_prec=dprec)
    if fac_shifted is None:
        return False, -math.inf, kappa2_bound

    mat_full = [
        [
            make_scalar(
                float(2 * ata[i][j])
                + (s_vals[i] - float(inc.degrees[i]) if i == j else 0.0),
                ledger,
                mode=mode,
                decimal_prec=dprec,
            )
            for j in range(n)
        ]
        for i in range(n)
    ]
    fac_cert: LDLTFactor | None = ldlt_factor(mat_full, ledger, mode=mode, decimal_prec=dprec)
    if fac_cert is None:
        return False, -math.inf, kappa2_bound

    y_cert = [0.0] * m
    best_d_spec = -math.inf
    eps_mach = 2.0**-53
    cert_tol_coeff = float(n * n) * eps_mach * kappa2_bound
    alpha_y = cfg.alpha_y
    alpha_s = cfg.alpha_s
    b_y = cfg.B_y
    s_interval = max(1, min(n, 4))

    for step_idx in range(max_steps):
        # Compute b = A^T y - 2*d - s and rhs = -0.5 * b
        rhs_s = []
        neg_half_b = [0.0] * n
        for i in range(n):
            aty_i = 0.0
            for c_idx, coeff in inc.var_clauses[i]:
                aty_i += coeff * y_cert[c_idx]
            bi = aty_i - 2.0 * float(inc.degrees[i]) - s_vals[i]
            nhb = -0.5 * bi
            neg_half_b[i] = nhb
            rhs_s.append(make_scalar(nhb, ledger, mode=mode, decimal_prec=dprec))

        x_dual_s = ldlt_solve(fac_cert, rhs_s)
        x_dual = [float(v) for v in x_dual_s]

        y_sum = sum(y_cert)
        quad_term = 0.0
        x_norm_sq = 0.0
        for i in range(n):
            xi = x_dual[i]
            quad_term += xi * neg_half_b[i]
            x_norm_sq += xi * xi
        d_spec = float(m) - y_sum - quad_term
        ledger.record_float(d_spec, count_op=True)
        if math.isfinite(d_spec) and d_spec > best_d_spec:
            best_d_spec = d_spec

        eps_cert = 1e-6 + cert_tol_coeff * x_norm_sq
        if math.isfinite(d_spec) and d_spec > eps_cert:
            return True, d_spec, kappa2_bound

        # Ascent step on y_cert: grad_y[j] = (A x_dual)[j] - 1
        for j, terms in enumerate(inc.clause_terms):
            ax_j = 0.0
            for v_idx, coeff in terms:
                ax_j += coeff * x_dual[v_idx]
            yv = y_cert[j] + alpha_y * (ax_j - 1.0)
            if yv > b_y:
                yv = b_y
            elif yv < -b_y:
                yv = -b_y
            y_cert[j] = yv

        # Periodic square-root-free LDL^T backtracking ascent on s_cert: grad_s[i] = x_i^2 - x_i
        if (step_idx % s_interval) == 0 and n <= 35:
            step_s = alpha_s
            for _ in range(4):
                s_cand = []
                for i in range(n):
                    gs = x_dual[i] * x_dual[i] - x_dual[i]
                    sc = s_vals[i] + step_s * gs
                    if sc > b_s_eff:
                        sc = b_s_eff
                    elif sc < -b_s_eff:
                        sc = -b_s_eff
                    if inc.degrees[i] == 0 and sc < 2.0 * eps_chol:
                        sc = 2.0 * eps_chol
                    s_cand.append(sc)
                m_sh = [
                    [
                        make_scalar(
                            float(2 * ata[i][j])
                            + (s_cand[i] - float(inc.degrees[i]) - eps_chol if i == j else 0.0),
                            ledger,
                            mode=mode,
                            decimal_prec=dprec,
                        )
                        for j in range(n)
                    ]
                    for i in range(n)
                ]
                if ldlt_factor(m_sh, ledger, mode=mode, decimal_prec=dprec) is not None:
                    m_fl = [
                        [
                            make_scalar(
                                float(2 * ata[i][j])
                                + (s_cand[i] - float(inc.degrees[i]) if i == j else 0.0),
                                ledger,
                                mode=mode,
                                decimal_prec=dprec,
                            )
                            for j in range(n)
                        ]
                        for i in range(n)
                    ]
                    new_fac = ldlt_factor(m_fl, ledger, mode=mode, decimal_prec=dprec)
                    if new_fac is not None:
                        s_vals = s_cand
                        fac_cert = new_fac
                        break
                step_s *= 0.5

    return False, best_d_spec, kappa2_bound


def _expand_assignment(lift: _RLTLift, x_compact: Sequence[int]) -> list[int]:
    """Expand compact quotient assignment in {0,1}^k back to full {0,1}^n."""
    out = [0] * lift.n_orig
    for i in range(lift.n_orig):
        r = _uf_find(lift.parent, i)
        fv = lift.forced.get(r)
        if fv is not None:
            out[i] = fv
        else:
            out[i] = x_compact[lift.root_to_idx[r]]
    return out


def _greedy_prop_round(
    x_vals: Sequence[float],
    lift: _RLTLift,
    var_eq_clauses: Sequence[Sequence[int]],
    ledger: BitLedger,
) -> list[int]:
    """Deterministic single-pass greedy conflict + unit-propagation rounding (O(m), no backtracking)."""
    k = len(lift.active_roots)
    order = sorted(range(k), key=lambda i: (-x_vals[i], i))
    assign: list[int | None] = [None] * k
    eq_clauses = lift.eq_clauses
    adj = lift.adj_compact

    def propagate_from(start_var: int) -> None:
        q: deque[int] = deque([start_var])
        while q:
            u = q.popleft()
            val_u = assign[u]
            if val_u == 1:
                for nb in adj[u]:
                    if assign[nb] is None:
                        assign[nb] = 0
                        ledger.record_int(0, count_op=True)
                        q.append(nb)
            elif val_u == 0:
                for c_idx in var_eq_clauses[u]:
                    cl = eq_clauses[c_idx]
                    ones = 0
                    unass = -1
                    unass_cnt = 0
                    for v in cl:
                        av = assign[v]
                        if av == 1:
                            ones += 1
                            break
                        if av is None:
                            unass = v
                            unass_cnt += 1
                    if ones == 0 and unass_cnt == 1:
                        # Check if setting unass=1 conflicts with an already-1 neighbor
                        conflict = False
                        for nb in adj[unass]:
                            if assign[nb] == 1:
                                conflict = True
                                break
                        if not conflict:
                            assign[unass] = 1
                            ledger.record_int(1, count_op=True)
                            q.append(unass)

    for i in order:
        if assign[i] is not None:
            continue
        # Try setting i = 1 if no neighbor is already 1
        can_one = True
        for nb in adj[i]:
            if assign[nb] == 1:
                can_one = False
                break
        if can_one:
            assign[i] = 1
            ledger.record_int(1, count_op=True)
            propagate_from(i)
        else:
            assign[i] = 0
            ledger.record_int(0, count_op=True)
            propagate_from(i)

    compact = [1 if v == 1 else 0 for v in assign]
    return _expand_assignment(lift, compact)


def solve_track_a(
    instance: Monotone1in3Instance,
    config: SolverConfig | None = None,
) -> SolverResult:
    """Solve Monotone 1-in-3 SAT via Track A: Sparse Degree-3 / Local Clique SoS & RLT Lift."""
    t_start = time.perf_counter()
    cfg = config or SolverConfig()
    n = instance.n_vars
    m = instance.m_clauses

    ledger = BitLedger(
        max_int_bits_limit=cfg.max_int_bits_limit,
        max_fraction_bits_limit=cfg.max_fraction_bits_limit,
        raise_on_guardrail=True,
    )

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
        inc = build_incidence(instance)
        b_s_eff_float = max(cfg.B_s, float(inc.max_degree) + 2.0 * cfg.eps_chol + 1.0)
        kappa2_bound = (18.0 * m + b_s_eff_float) / cfg.eps_chol

        # Stage 1: Sparse degree-2/3 RLT algebraic closure & local clique extraction
        lift = _build_rlt_lift(instance, inc, ledger)
        if not lift.unsat_proven and len(lift.active_roots) > 0:
            lift = _rlt1_lift_closure(instance, inc, lift, ledger)
        if lift.unsat_proven:
            return SolverResult(
                status="UNSAT_CERTIFIED",
                assignment=None,
                dual_certificate_value=1.0,
                iterations=1,
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
                termination_reason=lift.unsat_reason,
                final_x=tuple(0.0 for _ in range(n)),
                max_kappa2_cert_bound=kappa2_bound,
            )

        k = len(lift.active_roots)
        if k == 0:
            cand = _expand_assignment(lift, ())
            ver = verify_assignment(instance, cand)
            if ver.is_sat:
                return SolverResult(
                    status="SAT",
                    assignment=tuple(cand),
                    dual_certificate_value=0.0,
                    iterations=1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=0.0,
                    primal_res_l2=0.0,
                    integrality_gap=0.0,
                    dual_residual=0.0,
                    clause_violation_count=0,
                    bit_summary=ledger.summary(),
                    iteration_history=[],
                    verification=ver,
                    best_candidate=tuple(cand),
                    termination_reason="RLT_CLOSURE_SAT",
                    final_x=tuple(float(v) for v in cand),
                    max_kappa2_cert_bound=kappa2_bound,
                )

        # Stage 2: Exact integer-verified Farkas RLT + Clique dual ascent
        max_dual_iters = min(220, 4 * k + 60)
        farkas_unsat, best_dual, dual_iters = _run_rlt_farkas_dual(lift, ledger, max_dual_iters)
        if farkas_unsat:
            return SolverResult(
                status="UNSAT_CERTIFIED",
                assignment=None,
                dual_certificate_value=best_dual,
                iterations=dual_iters,
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
                termination_reason="RLT_CLIQUE_FARKAS_UNSAT",
                final_x=tuple(0.0 for _ in range(n)),
                max_kappa2_cert_bound=kappa2_bound,
            )

        # Stage 3: Square-root-free LDL^T spectral dual certificate (amortized small step budget)
        ldlt_steps = 12 if n <= 35 else 6
        ldlt_unsat, ldlt_d, kappa2_bound = _run_ldlt_spectral_dual(inc, ledger, cfg, max_steps=ldlt_steps)
        if math.isfinite(ldlt_d) and ldlt_d > best_dual:
            best_dual = ldlt_d
        if ldlt_unsat:
            return SolverResult(
                status="UNSAT_CERTIFIED",
                assignment=None,
                dual_certificate_value=ldlt_d,
                iterations=dual_iters + ldlt_steps,
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
                termination_reason="LDLT_SPECTRAL_UNSAT",
                final_x=tuple(0.0 for _ in range(n)),
                max_kappa2_cert_bound=kappa2_bound,
            )

        # Stage 4: Enriched RLT-Quotient Fisher-Rao / Primal-Dual Flow + Clique Repulsion
        max_iters = cfg.max_iters if cfg.max_iters is not None else min(900, 12 * n + 180)
        m_eq = len(lift.eq_clauses)
        inv_sqrt_m = 1.0 / math.sqrt(max(1, m_eq))

        var_eq_clauses: list[list[int]] = [[] for _ in range(k)]
        for c_idx, cl in enumerate(lift.eq_clauses):
            for v in cl:
                var_eq_clauses[v].append(c_idx)

        # Precompute degree-based diagonal preconditioner for compact variables
        deg_c = [max(1, len(var_eq_clauses[i])) for i in range(k)]
        inv_diag_precond = [1.0 / (1.0 + 0.5 * float(deg_c[i])) for i in range(k)]

        two_pi = 2.0 * math.pi
        phi_base = math.acos(1.0 / 3.0)
        phi = [
            (phi_base + cfg.delta_0 * math.sin(two_pi * float(i + 1) / float(k + 1))) % two_pi
            for i in range(k)
        ]
        p = [0.0] * k
        lam = [0.0] * m_eq
        x_prev: list[float] | None = None

        kappa_w = cfg.kappa_w
        rho = cfg.rho
        alpha_k = cfg.alpha_k
        alpha_clq = 0.85
        alpha_imp = 0.75
        mu_damp = cfg.mu_damp
        tau_step = cfg.tau_step
        gamma_wf = cfg.gamma_wf
        theta_pdhg = cfg.theta_pdhg
        eta_d = cfg.eta_d
        one_minus_damp_d = 1.0 - eta_d * cfg.delta_d
        b_lam = cfg.B_lambda
        omega_1 = math.pi / 3.0
        omega_2 = math.pi * 0.5
        restart_period = max(45, min(140, 2 * k + 30))

        best_r2 = math.inf
        stall_counter = 0
        restart_idx = 0
        best_candidate: tuple[int, ...] | None = None
        best_violations = m + 1
        last_res_inf = 1.0
        last_res_l2 = 1.0
        last_igap = 0.5
        last_dual_res = 0.0
        last_x = [1.0 / 3.0] * k
        iter_history: list[dict[str, Any]] = []

        for t in range(max_iters):
            if cfg.max_time_sec is not None and (time.perf_counter() - t_start) >= cfg.max_time_sec:
                full_x = [
                    float(lift.forced[_uf_find(lift.parent, i)])
                    if _uf_find(lift.parent, i) in lift.forced
                    else last_x[lift.root_to_idx[_uf_find(lift.parent, i)]]
                    for i in range(n)
                ]
                return SolverResult(
                    status="UNRESOLVED",
                    assignment=None,
                    dual_certificate_value=best_dual if math.isfinite(best_dual) else -math.inf,
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
                    final_x=tuple(full_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            ledger.begin_iteration(t)

            # 1. Manifold evaluation on torus
            sin_phi = [math.sin(ph) for ph in phi]
            sigma = [math.cos(ph) for ph in phi]
            x = [0.5 * (1.0 - sg) for sg in sigma]
            last_x = x

            # Clause residuals & metrics
            r = [0.0] * m_eq
            w = [0.0] * m_eq
            res_inf = 0.0
            r2_sq = 0.0
            for j, cl in enumerate(lift.eq_clauses):
                s_cl = 0.0
                for v in cl:
                    s_cl += x[v]
                rj = s_cl - 1.0
                r[j] = rj
                w[j] = 1.0 + kappa_w * rj * rj
                ar = abs(rj)
                if ar > res_inf:
                    res_inf = ar
                r2_sq += rj * rj

            r2_norm = math.sqrt(r2_sq) if math.isfinite(r2_sq) else r2_sq
            res_l2 = r2_norm * inv_sqrt_m
            igap = 0.0
            for xi in x:
                g_i = xi if xi <= 0.5 else (1.0 - xi)
                if g_i > igap:
                    igap = g_i

            ledger.record_float(res_inf, count_op=True)
            ledger.record_float(res_l2, count_op=True)
            ledger.record_float(igap, count_op=True)

            last_res_inf = res_inf
            last_res_l2 = res_l2
            last_igap = igap

            if not (math.isfinite(res_inf) and math.isfinite(res_l2)):
                ledger.end_iteration()
                return SolverResult(
                    status="OVERFLOW",
                    assignment=None,
                    dual_certificate_value=best_dual if math.isfinite(best_dual) else -math.inf,
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
                    final_x=tuple(0.0 for _ in range(n)),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            # 2. Rounding & deterministic verifier check
            cand_thr = _expand_assignment(lift, [1 if xi >= 0.5 else 0 for xi in x])
            ver_thr = verify_assignment(instance, cand_thr)
            if ver_thr.is_sat:
                bit_snap = ledger.end_iteration()
                if cfg.record_iter_history:
                    iter_history.append({
                        "iteration": t,
                        "primal_res_inf": res_inf,
                        "primal_res_l2": res_l2,
                        "integrality_gap": igap,
                        "d_spec": best_dual,
                        **bit_snap,
                    })
                full_x = [
                    float(lift.forced[_uf_find(lift.parent, i)])
                    if _uf_find(lift.parent, i) in lift.forced
                    else x[lift.root_to_idx[_uf_find(lift.parent, i)]]
                    for i in range(n)
                ]
                return SolverResult(
                    status="SAT",
                    assignment=tuple(cand_thr),
                    dual_certificate_value=best_dual if math.isfinite(best_dual) else 0.0,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=res_inf,
                    primal_res_l2=res_l2,
                    integrality_gap=igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=0,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=ver_thr,
                    best_candidate=tuple(cand_thr),
                    termination_reason="SAT_FOUND",
                    final_x=tuple(full_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            cand_greedy = _greedy_prop_round(x, lift, var_eq_clauses, ledger)
            ver_greedy = verify_assignment(instance, cand_greedy)
            if ver_greedy.is_sat:
                bit_snap = ledger.end_iteration()
                if cfg.record_iter_history:
                    iter_history.append({
                        "iteration": t,
                        "primal_res_inf": res_inf,
                        "primal_res_l2": res_l2,
                        "integrality_gap": igap,
                        "d_spec": best_dual,
                        **bit_snap,
                    })
                full_x = [
                    float(lift.forced[_uf_find(lift.parent, i)])
                    if _uf_find(lift.parent, i) in lift.forced
                    else x[lift.root_to_idx[_uf_find(lift.parent, i)]]
                    for i in range(n)
                ]
                return SolverResult(
                    status="SAT",
                    assignment=tuple(cand_greedy),
                    dual_certificate_value=best_dual if math.isfinite(best_dual) else 0.0,
                    iterations=t + 1,
                    runtime_sec=time.perf_counter() - t_start,
                    primal_res_inf=res_inf,
                    primal_res_l2=res_l2,
                    integrality_gap=igap,
                    dual_residual=last_dual_res,
                    clause_violation_count=0,
                    bit_summary=ledger.summary(),
                    iteration_history=iter_history,
                    verification=ver_greedy,
                    best_candidate=tuple(cand_greedy),
                    termination_reason="SAT_FOUND",
                    final_x=tuple(full_x),
                    max_kappa2_cert_bound=kappa2_bound,
                )

            for cand, ver_c in ((cand_thr, ver_thr), (cand_greedy, ver_greedy)):
                vc = len(ver_c.violated_clauses)
                if vc < best_violations:
                    best_violations = vc
                    best_candidate = tuple(cand)

            # 3. Enriched primal-dual x-gradient:
            #    clauses + quotient conflict K + clique repulsion + RLT implication penalty
            g_x = [0.0] * k
            for j, cl in enumerate(lift.eq_clauses):
                rj = r[j]
                drive = (w[j] + rho) * rj + lam[j]
                for v in cl:
                    g_x[v] += drive

            # Pairwise conflict repulsion K_compact * x
            for i in range(k):
                s_nb = 0.0
                for nb in lift.adj_compact[i]:
                    s_nb += x[nb]
                g_x[i] += alpha_k * s_nb

            # Clique repulsion: sum_{i in C} x_i <= 1
            for clq in lift.cliques:
                s_c = 0.0
                for v in clq:
                    s_c += x[v]
                exc = s_c - 1.0
                if exc > 0.0:
                    pen = alpha_clq * exc
                    for v in clq:
                        g_x[v] += pen

            # RLT implication penalty: x_d <= x_c
            for d, c in lift.implications:
                viol = x[d] - x[c]
                if viol > 0.0:
                    pen = alpha_imp * viol
                    g_x[d] += pen
                    g_x[c] -= pen

            # 4. Walsh-Fourier clause gradient + Boolean pinning + Fisher-Rao pullback
            dU_dsigma = [0.0] * k
            for j, cl in enumerate(lift.eq_clauses):
                wj = w[j]
                if len(cl) == 3:
                    a, b, c = cl
                    sa, sb, sc = sigma[a], sigma[b], sigma[c]
                    dU_dsigma[a] += wj * (-1.0 + sb + sc + 3.0 * sb * sc) * 0.125
                    dU_dsigma[b] += wj * (-1.0 + sa + sc + 3.0 * sa * sc) * 0.125
                    dU_dsigma[c] += wj * (-1.0 + sa + sb + 3.0 * sa * sb) * 0.125
                elif len(cl) == 2:
                    # x_a + x_b = 1 <=> sigma_a + sigma_b = 0 -> U = (1 + sigma_a*sigma_b)/2
                    a, b = cl
                    dU_dsigma[a] += 0.5 * wj * sigma[b]
                    dU_dsigma[b] += 0.5 * wj * sigma[a]

            phase_pos = (t % restart_period) / float(restart_period)
            beta_t = cfg.beta_min + (cfg.beta_max - cfg.beta_min) * phase_pos

            g_phi = [0.0] * k
            for i in range(k):
                si = sin_phi[i]
                g_val = 0.5 * si * g_x[i] - gamma_wf * si * dU_dsigma[i] + beta_t * si * sigma[i]
                g_phi[i] = g_val * inv_diag_precond[i]
                ledger.record_float(g_phi[i], count_op=True)

            # 5. Stagnation kick & deterministic phase restart
            if r2_norm < best_r2 - cfg.eps_imp:
                best_r2 = r2_norm
                stall_counter = 0
            else:
                stall_counter += 1

            do_restart = (t > 0) and ((t % restart_period) == 0)
            if do_restart:
                restart_idx += 1
                stall_counter = 0
                best_r2 = math.inf
                # Deterministic golden-angle phase perturbation (no randomness)
                phi_shift = 0.6180339887498949 * float(restart_idx)
                for i in range(k):
                    ang = two_pi * ((float(i + 1) * phi_shift + 0.37 * float(restart_idx)) % 1.0)
                    phi[i] = (phi_base + 0.55 * math.sin(ang)) % two_pi
                    p[i] = 0.0
                    ledger.record_float(phi[i], count_op=True)
                for j in range(m_eq):
                    lam[j] *= 0.25
                x_prev = None
                ledger.end_iteration()
                continue

            use_kick = stall_counter >= cfg.w_stall
            if use_kick:
                stall_counter = 0

            # 6. Geodesic torus momentum update & PDHG dual multiplier update
            dual_res = 0.0
            for i in range(k):
                kick_i = 0.0
                if use_kick:
                    arg1 = (two_pi * float(i)) / 3.0 + float(t) * omega_1
                    arg2 = (two_pi * float(i)) / 5.0 + float(t) * omega_2
                    kick_i = cfg.eps_kick * (math.cos(arg1) - math.cos(arg2))
                pi_new = mu_damp * p[i] - tau_step * g_phi[i] + kick_i
                dp = abs(pi_new - p[i])
                if dp > dual_res:
                    dual_res = dp
                p[i] = pi_new
                phi[i] = (phi[i] + pi_new) % two_pi
                ledger.record_float(phi[i], count_op=True)

            if x_prev is None:
                x_bar = x
            else:
                x_bar = [x[i] + theta_pdhg * (x[i] - x_prev[i]) for i in range(k)]

            for j, cl in enumerate(lift.eq_clauses):
                ax_b = 0.0
                for v in cl:
                    ax_b += x_bar[v]
                lj_new = one_minus_damp_d * lam[j] + eta_d * (ax_b - 1.0)
                if lj_new > b_lam:
                    lj_new = b_lam
                elif lj_new < -b_lam:
                    lj_new = -b_lam
                dl = abs(lj_new - lam[j])
                if dl > dual_res:
                    dual_res = dl
                lam[j] = lj_new
            ledger.record_float(dual_res, count_op=True)
            last_dual_res = dual_res
            x_prev = x

            bit_snap = ledger.end_iteration()
            if cfg.record_iter_history:
                iter_history.append({
                    "iteration": t,
                    "primal_res_inf": res_inf,
                    "primal_res_l2": res_l2,
                    "integrality_gap": igap,
                    "d_spec": best_dual if math.isfinite(best_dual) else None,
                    **bit_snap,
                })

            if ledger.nan_count > 0 or ledger.overflow_count > 0 or ledger.guardrail_tripped:
                return SolverResult(
                    status="OVERFLOW",
                    assignment=None,
                    dual_certificate_value=best_dual if math.isfinite(best_dual) else -math.inf,
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
                    final_x=tuple(0.0 for _ in range(n)),
                    max_kappa2_cert_bound=kappa2_bound,
                )

        full_x = [
            float(lift.forced[_uf_find(lift.parent, i)])
            if _uf_find(lift.parent, i) in lift.forced
            else last_x[lift.root_to_idx[_uf_find(lift.parent, i)]]
            for i in range(n)
        ]
        return SolverResult(
            status="UNRESOLVED",
            assignment=None,
            dual_certificate_value=best_dual if math.isfinite(best_dual) else -math.inf,
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
            final_x=tuple(full_x),
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
