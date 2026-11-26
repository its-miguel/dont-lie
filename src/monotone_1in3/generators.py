"""Reproducible hard-instance benchmark generators and harness-only DPLL oracle (R3).

STRICT ISOLATION: Never import this module from solver.py or primitives.py.
The DPLL exact solver here is exclusively for ground-truth labeling of
unconditioned random F1 instances and unit-test cross-checking.
"""

from __future__ import annotations

from dataclasses import dataclass
import random
from typing import Sequence

from .instance import Monotone1in3Instance
from .verifier import verify_assignment


@dataclass(frozen=True)
class BenchmarkCase:
    """Single benchmark instance paired with family metadata and verified ground truth."""

    instance_id: str
    family: str
    n_vars: int
    m_clauses: int
    alpha: float
    seed: int
    ground_truth: str  # "SAT" | "UNSAT"
    instance: Monotone1in3Instance
    witness: tuple[int, ...] | None = None


# ---------------------------------------------------------------------------
# Harness-only exact DPLL oracle for Monotone 1-in-3 SAT (n <= 60)
# ---------------------------------------------------------------------------

def exact_dpll_solve(
    instance: Monotone1in3Instance,
) -> tuple[bool, tuple[int, ...] | None]:
    """Exact deterministic backtracking + propagation solver for Monotone 1-in-3 SAT.

    Used ONLY by the test harness to label random F1 instances and validate
    reductions in unit tests. Never imported by solver.py or primitives.py.
    """
    n = instance.n_vars
    clauses = instance.clauses
    m = len(clauses)
    if m == 0:
        return True, tuple([0] * n)
    if n == 0:
        return False, None

    var_to_clauses: list[list[int]] = [[] for _ in range(n)]
    for c_idx, (a, b, c) in enumerate(clauses):
        var_to_clauses[a].append(c_idx)
        if b != a:
            var_to_clauses[b].append(c_idx)
        if c != a and c != b:
            var_to_clauses[c].append(c_idx)

    assign: list[int | None] = [None] * n
    trail: list[int] = []

    def propagate(start_queue: list[int]) -> bool:
        queue = list(start_queue)
        seen_q = set(queue)
        while queue:
            c_idx = queue.pop()
            seen_q.discard(c_idx)
            a, b, c = clauses[c_idx]
            ones = 0
            zeros = 0
            unassigned: list[int] = []
            for v in (a, b, c):
                val = assign[v]
                if val == 1:
                    ones += 1
                elif val == 0:
                    zeros += 1
                else:
                    unassigned.append(v)
            if ones > 1:
                return False
            if ones == 1:
                for v in unassigned:
                    if assign[v] is None:
                        assign[v] = 0
                        trail.append(v)
                        for nc in var_to_clauses[v]:
                            if nc not in seen_q:
                                queue.append(nc)
                                seen_q.add(nc)
            else:  # ones == 0
                if zeros == 3:
                    return False
                if len(unassigned) == 1:
                    v = unassigned[0]
                    assign[v] = 1
                    trail.append(v)
                    for nc in var_to_clauses[v]:
                        if nc not in seen_q:
                            queue.append(nc)
                            seen_q.add(nc)
                elif len(unassigned) > 1 and len(set(unassigned)) == 1:
                    # Repeated unassigned variable: setting it to 1 gives sum >= 2
                    return False
        return True

    def backtrack() -> bool:
        best_v = -1
        best_score = -1
        for v in range(n):
            if assign[v] is None:
                deg = len(var_to_clauses[v])
                if deg > best_score:
                    best_score = deg
                    best_v = v
        if best_v == -1:
            return True

        for choice in (1, 0):
            mark = len(trail)
            assign[best_v] = choice
            trail.append(best_v)
            if propagate(var_to_clauses[best_v]):
                if backtrack():
                    return True
            while len(trail) > mark:
                v_pop = trail.pop()
                assign[v_pop] = None
        return False

    if not propagate(list(range(m))):
        return False, None
    if backtrack():
        sol = tuple(0 if v is None else v for v in assign)
        return True, sol
    return False, None


# ---------------------------------------------------------------------------
# Permutation & Clause-Shuffling Hygiene Helpers
# ---------------------------------------------------------------------------

def _permute_and_shuffle(
    n_vars: int,
    clauses: Sequence[tuple[int, int, int]],
    rng: random.Random,
    witness: Sequence[int] | None = None,
    metadata: dict | None = None,
) -> tuple[Monotone1in3Instance, tuple[int, ...] | None]:
    """Apply a random variable permutation in S_n and shuffle clause order."""
    # perm[old_idx] = new_idx
    new_indices = list(range(n_vars))
    rng.shuffle(new_indices)
    perm = new_indices

    mapped: list[tuple[int, int, int]] = []
    for a, b, c in clauses:
        cl = [perm[a], perm[b], perm[c]]
        rng.shuffle(cl)
        mapped.append((cl[0], cl[1], cl[2]))
    rng.shuffle(mapped)

    inst = Monotone1in3Instance(
        n_vars=n_vars,
        clauses=tuple(mapped),
        metadata=metadata or {},
    )
    ok, errs = inst.validate_hygiene()
    if not ok:
        raise ValueError(f"Generated instance failed hygiene check: {errs[:3]}")

    mapped_witness: tuple[int, ...] | None = None
    if witness is not None:
        w_out = [0] * n_vars
        for old_i, val in enumerate(witness):
            w_out[perm[old_i]] = val
        mapped_witness = tuple(w_out)
        vr = verify_assignment(inst, mapped_witness)
        if not vr.is_sat:
            raise ValueError(f"Generated witness failed verifier: {vr.violated_clauses[:3]}")

    return inst, mapped_witness


# ---------------------------------------------------------------------------
# F1: Critical-Threshold Random G^(3)(n, m)
# ---------------------------------------------------------------------------

_ALPHA_50_M = {15: 12, 30: 22, 60: 41}


def generate_random_f1(n_vars: int, m_clauses: int, seed: int) -> BenchmarkCase:
    """Generate an unconditioned distinct-variable G^(3)(n, m) instance."""
    rng = random.Random(seed)
    seen: set[tuple[int, int, int]] = set()
    clauses: list[tuple[int, int, int]] = []
    while len(clauses) < m_clauses:
        a, b, c = sorted(rng.sample(range(n_vars), 3))
        key = (a, b, c)
        if key not in seen:
            seen.add(key)
            cl = [a, b, c]
            rng.shuffle(cl)
            clauses.append((cl[0], cl[1], cl[2]))
    rng.shuffle(clauses)
    alpha = m_clauses / n_vars
    inst = Monotone1in3Instance(
        n_vars=n_vars,
        clauses=tuple(clauses),
        metadata={"family": "F1_random", "alpha": alpha, "seed": seed},
    )
    is_sat, witness = exact_dpll_solve(inst)
    return BenchmarkCase(
        instance_id=f"F1_n{n_vars}_m{m_clauses}_s{seed}",
        family="F1_random",
        n_vars=n_vars,
        m_clauses=m_clauses,
        alpha=alpha,
        seed=seed,
        ground_truth="SAT" if is_sat else "UNSAT",
        instance=inst,
        witness=witness,
    )


# ---------------------------------------------------------------------------
# F2: Degree-Balanced Planted SAT (|S1| = floor(n/3), deg >= 1)
# ---------------------------------------------------------------------------

def generate_planted_f2(n_vars: int, m_clauses: int, seed: int) -> BenchmarkCase:
    """Generate a degree-balanced planted SAT instance with |S1|=floor(n/3) and deg >= 1."""
    rng = random.Random(seed)
    k1 = n_vars // 3
    all_vars = list(range(n_vars))
    rng.shuffle(all_vars)
    s1 = all_vars[:k1]
    s0 = all_vars[k1:]
    witness = [0] * n_vars
    for v in s1:
        witness[v] = 1

    seen: set[tuple[int, int, int]] = set()
    clauses: list[tuple[int, int, int]] = []
    deg = [0] * n_vars

    def add_clause(u1: int, u0a: int, u0b: int) -> bool:
        if u0a == u0b:
            return False
        key = tuple(sorted((u1, u0a, u0b)))
        if key in seen:  # type: ignore[arg-type]
            return False
        seen.add(key)  # type: ignore[arg-type]
        cl = [u1, u0a, u0b]
        rng.shuffle(cl)
        clauses.append((cl[0], cl[1], cl[2]))
        deg[u1] += 1
        deg[u0a] += 1
        deg[u0b] += 1
        return True

    # Ensure every variable in S1 and S0 achieves degree >= 1 first
    for v in s1:
        if deg[v] == 0 and len(clauses) < m_clauses:
            for _ in range(100):
                u0a, u0b = rng.sample(s0, 2)
                if add_clause(v, u0a, u0b):
                    break

    for v in s0:
        if deg[v] == 0 and len(clauses) < m_clauses:
            uncovered = [u for u in s0 if u != v and deg[u] == 0]
            added = False
            if uncovered:
                rng.shuffle(uncovered)
                u1_candidates = list(s1)
                rng.shuffle(u1_candidates)
                for other_s0 in uncovered:
                    for u1 in u1_candidates:
                        if add_clause(u1, v, other_s0):
                            added = True
                            break
                    if added:
                        break
            if not added:
                for _ in range(100):
                    u1 = rng.choice(s1)
                    other_s0 = rng.choice(s0)
                    if other_s0 != v and add_clause(u1, v, other_s0):
                        break

    # Fill remaining clauses up to m_clauses balanced across S1 / S0
    while len(clauses) < m_clauses:
        u1 = rng.choice(s1)
        u0a, u0b = rng.sample(s0, 2)
        add_clause(u1, u0a, u0b)

    if min(deg) < 1:
        raise ValueError(f"F2 degree invariant violated: min(deg)={min(deg)} < 1")

    rng.shuffle(clauses)
    alpha = m_clauses / n_vars
    inst = Monotone1in3Instance(
        n_vars=n_vars,
        clauses=tuple(clauses),
        metadata={"family": "F2_planted_sat", "alpha": alpha, "seed": seed},
    )
    ok, errs = inst.validate_hygiene()
    if not ok:
        raise ValueError(f"F2 hygiene failure: {errs[:3]}")
    vr = verify_assignment(inst, witness)
    if not vr.is_sat:
        raise ValueError(f"F2 witness failed verifier: {vr.violated_clauses[:3]}")

    return BenchmarkCase(
        instance_id=f"F2_n{n_vars}_m{m_clauses}_s{seed}",
        family="F2_planted_sat",
        n_vars=n_vars,
        m_clauses=m_clauses,
        alpha=alpha,
        seed=seed,
        ground_truth="SAT",
        instance=inst,
        witness=tuple(witness),
    )


# ---------------------------------------------------------------------------
# F3a / F3b: Tseitin XOR Reductions (Exact n = 15, 30, 60)
# ---------------------------------------------------------------------------

class _ClauseBuilder:
    """Helper to allocate variables and build gadgets cleanly."""

    def __init__(self) -> None:
        self.n_vars = 0
        self.clauses: list[tuple[int, int, int]] = []

    def new_var(self) -> int:
        v = self.n_vars
        self.n_vars += 1
        return v

    def add(self, a: int, b: int, c: int) -> None:
        self.clauses.append((a, b, c))

    def add_const_gadget(self, odd_pad: bool = False) -> tuple[int, int]:
        """Add constant-forcing gadget returning (z0, z1) with z0=0, z1=1."""
        z1 = self.new_var()
        z0 = self.new_var()
        z0p = self.new_var()
        z0pp = self.new_var()
        self.add(z1, z0, z0p)
        self.add(z1, z0, z0pp)
        self.add(z1, z0p, z0pp)
        if odd_pad:
            z0ppp = self.new_var()
            self.add(z1, z0, z0ppp)
        return z0, z1


def _solve_gf2_and_build_tseitin(
    n_vertices: int,
    edges: Sequence[tuple[int, int]],
    charges: Sequence[int],
    need_z0: bool,
    odd_z0_pad: bool,
    rng: random.Random,
    expect_sat: bool,
    family: str,
    seed: int,
) -> BenchmarkCase:
    """Reduce a connected Tseitin graph (deg 2/3) to Monotone 1-in-3 SAT."""
    cb = _ClauseBuilder()
    e_vars = [cb.new_var() for _ in edges]
    inc: list[list[int]] = [[] for _ in range(n_vertices)]
    for e_idx, (u, v) in enumerate(edges):
        inc[u].append(e_idx)
        inc[v].append(e_idx)

    z0 = -1
    if need_z0:
        z0, z1 = cb.add_const_gadget(odd_pad=odd_z0_pad)
    else:
        z1 = -1

    # Allocate gadget variables and emit clauses
    # Track vertex gadget specs so we can populate witness when SAT
    v_specs: list[tuple[int, list[int], int, tuple[int, ...]]] = []
    for v_idx in range(n_vertices):
        ev = [e_vars[e] for e in inc[v_idx]]
        deg = len(ev)
        sig = charges[v_idx]
        if deg == 3 and sig == 1:
            u_aux, w_aux, t_aux = cb.new_var(), cb.new_var(), cb.new_var()
            a, b, c = ev
            cb.add(a, u_aux, w_aux)
            cb.add(b, u_aux, t_aux)
            cb.add(c, w_aux, t_aux)
            v_specs.append((deg, ev, sig, (u_aux, w_aux, t_aux)))
        elif deg == 3 and sig == 0:
            if z0 < 0:
                raise ValueError("deg-3 sigma=0 requires z0 constant gadget")
            bar_a, u_aux, w_aux, t_aux = cb.new_var(), cb.new_var(), cb.new_var(), cb.new_var()
            a, b, c = ev
            cb.add(a, bar_a, z0)
            cb.add(bar_a, u_aux, w_aux)
            cb.add(b, u_aux, t_aux)
            cb.add(c, w_aux, t_aux)
            v_specs.append((deg, ev, sig, (bar_a, u_aux, w_aux, t_aux)))
        elif deg == 2 and sig == 1:
            if z0 < 0:
                raise ValueError("deg-2 sigma=1 requires z0 constant gadget")
            a, b = ev
            cb.add(a, b, z0)
            v_specs.append((deg, ev, sig, ()))
        elif deg == 2 and sig == 0:
            if z0 < 0:
                raise ValueError("deg-2 sigma=0 requires z0 constant gadget")
            t_aux = cb.new_var()
            a, b = ev
            cb.add(a, t_aux, z0)
            cb.add(b, t_aux, z0)
            v_specs.append((deg, ev, sig, (t_aux,)))
        else:
            raise ValueError(f"Unsupported vertex degree/charge: deg={deg}, sig={sig}")

    witness: list[int] | None = None
    if expect_sat:
        # Solve GF(2) linear system for edge variables
        n_e = len(edges)
        rows: list[list[int]] = []
        for v_idx in range(n_vertices):
            row = [0] * (n_e + 1)
            for e in inc[v_idx]:
                row[e] ^= 1
            row[n_e] = charges[v_idx]
            rows.append(row)
        # Gaussian elimination over GF(2)
        pivots: list[int] = []
        r = 0
        for col in range(n_e):
            piv = -1
            for rr in range(r, n_vertices):
                if rows[rr][col] == 1:
                    piv = rr
                    break
            if piv == -1:
                continue
            rows[r], rows[piv] = rows[piv], rows[r]
            for rr in range(n_vertices):
                if rr != r and rows[rr][col] == 1:
                    for cc in range(col, n_e + 1):
                        rows[rr][cc] ^= rows[r][cc]
            pivots.append(col)
            r += 1

        # Randomize free variables
        pivot_set = set(pivots)
        edge_sol = [rng.randint(0, 1) if c not in pivot_set else 0 for c in range(n_e)]
        for row_idx, pcol in enumerate(pivots):
            val = rows[row_idx][n_e]
            for c in range(pcol + 1, n_e):
                if rows[row_idx][c] == 1:
                    val ^= edge_sol[c]
            edge_sol[pcol] = val

        witness = [0] * cb.n_vars
        for e_i, val in enumerate(edge_sol):
            witness[e_vars[e_i]] = val
        if need_z0:
            witness[z1] = 1
        # Fill auxiliary witness values for each vertex gadget
        for deg, ev, sig, aux in v_specs:
            if deg == 3 and sig == 1:
                va, vb, vc = witness[ev[0]], witness[ev[1]], witness[ev[2]]
                u_aux, w_aux, t_aux = aux
                # (a,u,w), (b,u,t), (c,w,t)
                if (va, vb, vc) == (1, 1, 1):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 0, 0, 0
                elif (va, vb, vc) == (1, 0, 0):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 0, 0, 1
                elif (va, vb, vc) == (0, 1, 0):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 0, 1, 0
                elif (va, vb, vc) == (0, 0, 1):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 1, 0, 0
                else:
                    raise ValueError("GF(2) solution violated deg-3 sigma=1 parity")
            elif deg == 3 and sig == 0:
                va, vb, vc = witness[ev[0]], witness[ev[1]], witness[ev[2]]
                bar_a, u_aux, w_aux, t_aux = aux
                vba = 1 - va
                witness[bar_a] = vba
                if (vba, vb, vc) == (1, 1, 1):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 0, 0, 0
                elif (vba, vb, vc) == (1, 0, 0):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 0, 0, 1
                elif (vba, vb, vc) == (0, 1, 0):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 0, 1, 0
                elif (vba, vb, vc) == (0, 0, 1):
                    witness[u_aux], witness[w_aux], witness[t_aux] = 1, 0, 0
                else:
                    raise ValueError("GF(2) solution violated deg-3 sigma=0 parity")
            elif deg == 2 and sig == 0:
                t_aux = aux[0]
                witness[t_aux] = 1 - witness[ev[0]]

    n_total = cb.n_vars
    m_total = len(cb.clauses)
    inst, mapped_w = _permute_and_shuffle(
        n_total,
        cb.clauses,
        rng,
        witness=witness,
        metadata={"family": family, "alpha": m_total / n_total, "seed": seed},
    )
    return BenchmarkCase(
        instance_id=f"{family}_n{n_total}_m{m_total}_s{seed}",
        family=family,
        n_vars=n_total,
        m_clauses=m_total,
        alpha=m_total / n_total,
        seed=seed,
        ground_truth="SAT" if expect_sat else "UNSAT",
        instance=inst,
        witness=mapped_w,
    )


def _random_3regular_12(rng: random.Random) -> list[tuple[int, int]]:
    """Sample a simple connected 3-regular graph on 12 vertices via pairing + rejection."""
    n = 12
    while True:
        stubs = [v for v in range(n) for _ in range(3)]
        rng.shuffle(stubs)
        edges: list[tuple[int, int]] = []
        edge_set: set[tuple[int, int]] = set()
        valid = True
        for i in range(0, len(stubs), 2):
            u, v = stubs[i], stubs[i + 1]
            if u == v:
                valid = False
                break
            e = (u, v) if u < v else (v, u)
            if e in edge_set:
                valid = False
                break
            edge_set.add(e)
            edges.append(e)
        if not valid:
            continue
        # Connectivity BFS
        adj: list[list[int]] = [[] for _ in range(n)]
        for u, v in edges:
            adj[u].append(v)
            adj[v].append(u)
        seen = {0}
        stack = [0]
        while stack:
            cur = stack.pop()
            for nb in adj[cur]:
                if nb not in seen:
                    seen.add(nb)
                    stack.append(nb)
        if len(seen) == n:
            return edges


def generate_tseitin_f3(n_vars: int, sat: bool, seed: int) -> BenchmarkCase:
    """Generate exact-size (n=15, 30, 60) Tseitin XOR SAT (F3a) or UNSAT (F3b) instances."""
    rng = random.Random(seed)
    family = "F3a_tseitin_sat" if sat else "F3b_tseitin_unsat"

    if n_vars == 15:
        if sat:
            # K4 - e: V=4, E=5, degs=(3,3,2,2), charges=(1,1,1,1) -> 5 + 6 + 0 + 4 = 15
            edges = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3)]
            charges = [1, 1, 1, 1]
            return _solve_gf2_and_build_tseitin(
                4, edges, charges, need_z0=True, odd_z0_pad=False,
                rng=rng, expect_sat=True, family=family, seed=seed,
            )
        else:
            # V=3, E=4 multigraph: degs=(3,3,2), charges=(1,1,1), 5-var z0 -> 4 + 6 + 0 + 5 = 15
            edges = [(0, 1), (0, 1), (0, 2), (1, 2)]
            charges = [1, 1, 1]
            return _solve_gf2_and_build_tseitin(
                3, edges, charges, need_z0=True, odd_z0_pad=True,
                rng=rng, expect_sat=False, family=family, seed=seed,
            )

    if n_vars == 30:
        if sat:
            # Subdivided K4: V=8, E=10, four deg-3 (sig=1) + four deg-2 (sig=0) + 4-var z0 -> 30
            # Start from K4 on {0,1,2,3}, subdivide 4 edges (0,1)->4, (0,2)->5, (1,3)->6, (2,3)->7
            edges = [
                (0, 4), (4, 1),
                (0, 5), (5, 2),
                (0, 3),
                (1, 2),
                (1, 6), (6, 3),
                (2, 7), (7, 3),
            ]
            charges = [1, 1, 1, 1, 0, 0, 0, 0]
            return _solve_gf2_and_build_tseitin(
                8, edges, charges, need_z0=True, odd_z0_pad=False,
                rng=rng, expect_sat=True, family=family, seed=seed,
            )
        else:
            # Subdivided K4: V=7, E=9, four deg-3 + three deg-2 + 5-var z0 -> 30
            # Subdivide 3 edges of K4: (0,1)->4, (0,2)->5, (1,2)->6
            edges = [
                (0, 4), (4, 1),
                (0, 5), (5, 2),
                (1, 6), (6, 2),
                (0, 3), (1, 3), (2, 3),
            ]
            deg3_verts = [0, 1, 2, 3]
            rng.shuffle(deg3_verts)
            charges = [0] * 7
            # 3 deg-3 sig=1 (9 aux), 1 deg-3 sig=0 (4 aux), 3 deg-2 sig=0 (3 aux) -> sum=3 (odd)
            for dv in deg3_verts[:3]:
                charges[dv] = 1
            return _solve_gf2_and_build_tseitin(
                7, edges, charges, need_z0=True, odd_z0_pad=True,
                rng=rng, expect_sat=False, family=family, seed=seed,
            )

    if n_vars == 60:
        base_edges = _random_3regular_12(rng)
        if sat:
            # V=12, E=18, ten sig=1 (30 aux), two sig=0 (8 aux), 4-var z0 -> 18+30+8+4 = 60
            verts = list(range(12))
            rng.shuffle(verts)
            charges = [1] * 12
            charges[verts[0]] = 0
            charges[verts[1]] = 0
            return _solve_gf2_and_build_tseitin(
                12, base_edges, charges, need_z0=True, odd_z0_pad=False,
                rng=rng, expect_sat=True, family=family, seed=seed,
            )
        else:
            # Drop 1 edge: V=12, E=17 (ten deg-3, two deg-2)
            # Three deg-3 sig=1 (9 aux), seven deg-3 sig=0 (28 aux), two deg-2 sig=0 (2 aux), 4-var z0 -> 60
            drop_idx = rng.randrange(len(base_edges))
            du, dv = base_edges[drop_idx]
            edges = [e for idx, e in enumerate(base_edges) if idx != drop_idx]
            deg3_verts = [v for v in range(12) if v != du and v != dv]
            rng.shuffle(deg3_verts)
            charges = [0] * 12
            for v in deg3_verts[:3]:
                charges[v] = 1
            return _solve_gf2_and_build_tseitin(
                12, edges, charges, need_z0=True, odd_z0_pad=False,
                rng=rng, expect_sat=False, family=family, seed=seed,
            )

    raise ValueError(f"Tseitin F3 only supports n_vars in (15, 30, 60), got {n_vars}")


# ---------------------------------------------------------------------------
# F4a / F4b: Schaefer 3-SAT -> Monotone 1-in-3 SAT (Exact n = 15, 30, 60)
# ---------------------------------------------------------------------------

def _eval_3sat_or_aux(l1: int, l2: int, l3: int) -> tuple[int, int, int, int]:
    """Compute valid (a, b, c, d) for (~l1, a, b), (b, l2, c), (c, d, ~l3)."""
    nl1 = 1 - l1
    nl3 = 1 - l3
    for a in (0, 1):
        for b in (0, 1):
            if nl1 + a + b != 1:
                continue
            for c in (0, 1):
                if b + l2 + c != 1:
                    continue
                for d in (0, 1):
                    if c + d + nl3 == 1:
                        return (a, b, c, d)
    raise ValueError(f"3-SAT clause unsatisfied: {(l1, l2, l3)}")


def _build_schaefer_3sat_reduction(
    n_orig: int,
    clauses_3sat: Sequence[tuple[tuple[int, bool], tuple[int, bool], tuple[int, bool]]],
    odd_z0_pad: bool,
    planted_orig: Sequence[int] | None,
    rng: random.Random,
    family: str,
    seed: int,
) -> BenchmarkCase:
    """Reduce a 3-SAT formula (var, is_negated) literals to Monotone 1-in-3 SAT."""
    cb = _ClauseBuilder()
    pos_vars = [cb.new_var() for _ in range(n_orig)]
    neg_vars = [cb.new_var() for _ in range(n_orig)]
    z0, z1 = cb.add_const_gadget(odd_pad=odd_z0_pad)

    for i in range(n_orig):
        cb.add(pos_vars[i], neg_vars[i], z0)

    def lit_var(var_idx: int, is_neg: bool) -> int:
        return neg_vars[var_idx] if is_neg else pos_vars[var_idx]

    aux_tuples: list[tuple[int, int, int, int]] = []
    for (v1, n1), (v2, n2), (v3, n3) in clauses_3sat:
        a, b, c, d = cb.new_var(), cb.new_var(), cb.new_var(), cb.new_var()
        cb.add(lit_var(v1, not n1), a, b)
        cb.add(b, lit_var(v2, n2), c)
        cb.add(c, d, lit_var(v3, not n3))
        aux_tuples.append((a, b, c, d))

    witness: list[int] | None = None
    if planted_orig is not None:
        witness = [0] * cb.n_vars
        witness[z1] = 1
        for i in range(n_orig):
            witness[pos_vars[i]] = planted_orig[i]
            witness[neg_vars[i]] = 1 - planted_orig[i]
        for idx, ((v1, n1), (v2, n2), (v3, n3)) in enumerate(clauses_3sat):
            l1 = (1 - planted_orig[v1]) if n1 else planted_orig[v1]
            l2 = (1 - planted_orig[v2]) if n2 else planted_orig[v2]
            l3 = (1 - planted_orig[v3]) if n3 else planted_orig[v3]
            va, vb, vc, vd = _eval_3sat_or_aux(l1, l2, l3)
            a, b, c, d = aux_tuples[idx]
            witness[a], witness[b], witness[c], witness[d] = va, vb, vc, vd

    n_total = cb.n_vars
    m_total = len(cb.clauses)
    inst, mapped_w = _permute_and_shuffle(
        n_total,
        cb.clauses,
        rng,
        witness=witness,
        metadata={"family": family, "alpha": m_total / n_total, "seed": seed},
    )
    return BenchmarkCase(
        instance_id=f"{family}_n{n_total}_m{m_total}_s{seed}",
        family=family,
        n_vars=n_total,
        m_clauses=m_total,
        alpha=m_total / n_total,
        seed=seed,
        ground_truth="SAT" if planted_orig is not None else "UNSAT",
        instance=inst,
        witness=mapped_w,
    )


def generate_3sat_f4(n_vars: int, sat: bool, seed: int) -> BenchmarkCase:
    """Generate exact-size Schaefer 3-SAT->M1in3 SAT (F4a) and UNSAT (F4b) instances."""
    rng = random.Random(seed)
    if sat:
        family = "F4a_3sat_sat"
        if n_vars == 15:
            n_orig, m_orig, odd_pad = 3, 1, True
        elif n_vars == 30:
            n_orig, m_orig, odd_pad = 3, 5, False
        elif n_vars == 60:
            n_orig, m_orig, odd_pad = 4, 12, False
        else:
            raise ValueError(f"F4a supports n_vars in (15, 30, 60), got {n_vars}")

        planted = [rng.randint(0, 1) for _ in range(n_orig)]
        # Sample m_orig distinct 3-SAT clauses satisfied by `planted`
        seen_3sat: set[frozenset[tuple[int, bool]]] = set()
        clauses_3sat: list[tuple[tuple[int, bool], tuple[int, bool], tuple[int, bool]]] = []
        while len(clauses_3sat) < m_orig:
            vs = rng.sample(range(n_orig), 3)
            lits = tuple((v, bool(rng.randint(0, 1))) for v in vs)
            ok = any(
                ((1 - planted[v]) if is_neg else planted[v]) == 1
                for v, is_neg in lits
            )
            key = frozenset(lits)
            if ok and key not in seen_3sat:
                seen_3sat.add(key)
                clauses_3sat.append(lits)  # type: ignore[arg-type]

        return _build_schaefer_3sat_reduction(
            n_orig=n_orig,
            clauses_3sat=clauses_3sat,
            odd_z0_pad=odd_pad,
            planted_orig=planted,
            rng=rng,
            family=family,
            seed=seed,
        )

    else:
        if n_vars != 60:
            raise ValueError(f"F4b UNSAT 3-SAT reduction requires n_vars=60, got {n_vars}")
        family = "F4b_3sat_unsat"
        # All 8 distinct 3-SAT clauses on {0, 1, 2} form a minimal UNSAT core
        core_3sat: list[tuple[tuple[int, bool], tuple[int, bool], tuple[int, bool]]] = []
        for b0 in (False, True):
            for b1 in (False, True):
                for b2 in (False, True):
                    core_3sat.append(((0, b0), (1, b1), (2, b2)))
        # Add 4 coupled clauses involving variable 3 and pairs from {0, 1, 2}
        extra_pool: list[tuple[tuple[int, bool], tuple[int, bool], tuple[int, bool]]] = [
            ((0, False), (1, False), (3, False)),
            ((0, True), (2, False), (3, True)),
            ((1, True), (2, True), (3, False)),
            ((0, False), (2, True), (3, True)),
            ((1, False), (2, False), (3, True)),
            ((0, True), (1, True), (3, False)),
        ]
        rng.shuffle(extra_pool)
        clauses_3sat = core_3sat + extra_pool[:4]
        return _build_schaefer_3sat_reduction(
            n_orig=4,
            clauses_3sat=clauses_3sat,
            odd_z0_pad=False,
            planted_orig=None,
            rng=rng,
            family=family,
            seed=seed,
        )


# ---------------------------------------------------------------------------
# Full 140-Instance (and --fast 50-Instance) Benchmark Suite Assembler
# ---------------------------------------------------------------------------

def generate_benchmark_suite(seed: int = 20261124, fast: bool = False) -> list[BenchmarkCase]:
    """Assemble the complete reproducible benchmark suite across n in {15, 30, 60}."""
    cases: list[BenchmarkCase] = []
    s = seed

    for n in (15, 30, 60):
        m_626 = round(0.626 * n)
        m_23 = round((2 * n) / 3)
        m_50 = _ALPHA_50_M[n]

        # F1: Random Threshold Sweep (20 per n in full; 6 per n in fast)
        if fast:
            f1_counts = [(m_626, 2), (m_23, 2), (m_50, 2)]
        else:
            f1_counts = [(m_626, 6), (m_23, 6), (m_50, 8)]
        for m_val, count in f1_counts:
            for _ in range(count):
                s += 1
                cases.append(generate_random_f1(n, m_val, s))

        # F2: Degree-Balanced Planted SAT (10 per n in full; 4 per n in fast)
        f2_counts = [(m_626, 2), (m_50, 2)] if fast else [(m_626, 5), (m_50, 5)]
        for m_val, count in f2_counts:
            for _ in range(count):
                s += 1
                cases.append(generate_planted_f2(n, m_val, s))

        # F3a: Tseitin XOR SAT (5 per n in full; 2 per n in fast)
        n_f3a = 2 if fast else 5
        for _ in range(n_f3a):
            s += 1
            cases.append(generate_tseitin_f3(n, sat=True, seed=s))

        # F3b: Tseitin XOR UNSAT (5 per n in full; 2 per n in fast)
        n_f3b = 2 if fast else 5
        for _ in range(n_f3b):
            s += 1
            cases.append(generate_tseitin_f3(n, sat=False, seed=s))

        # F4a: 3-SAT -> M1in3 SAT (5 per n in full; 2 per n in fast)
        n_f4a = 2 if fast else 5
        for _ in range(n_f4a):
            s += 1
            cases.append(generate_3sat_f4(n, sat=True, seed=s))

    # F4b: 3-SAT -> M1in3 UNSAT at n=60 (5 in full; 2 in fast)
    n_f4b = 2 if fast else 5
    for _ in range(n_f4b):
        s += 1
        cases.append(generate_3sat_f4(60, sat=False, seed=s))

    return cases
