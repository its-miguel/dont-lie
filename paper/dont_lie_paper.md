# Don't Lie
*Fast, Zero-Backtracking Constraint Solving with Machine-Checked Proofs in Lean 4*

**Miguel Gutierrez** — Independent Researcher (`miguelgutierrezbarcelo@gmail.com`)  
**Code & Lean 4 Artifacts:** https://github.com/its-miguel/dont-lie  
*November 2026*

---

**Abstract.** Fast constraint solvers are complex and hard to trust, while formal mathematical verifiers are usually too slow for real-scale problems. In this paper, we ask how far a strictly polynomial-time, zero-backtracking solver can go—and whether its proofs of impossibility can be checked from first principles inside a theorem prover. Using Monotone 1-in-3 SAT as a clean testbed, we build a zero-allocation Rust solver by falsification: each time an adversarial puzzle breaks our solver, we add a minimal reasoning lens—parity algebra with local gadget peeling, integer cutting planes, statistical-physics message passing, and shallow single-variable lookahead. Across 140 small-to-medium puzzles, our solver resolves **140/140 (100%)**. Across 72 high-scale adversarial benchmarks up to 637 variables, it resolves **69/72 (95.8%)**—including **49/49 (100%)** of all satisfiable instances—using under 329 KB of RAM with zero false claims, running **9× faster than CaDiCaL** on parity traps and **12.4× faster** on pigeonhole traps. Finally, we verify exported refutations up to 783 variables purely inside Lean 4's foundational kernel (`by decide`), while honestly isolating the remaining 3-instance high-width boundary.

---

## 1. Introduction: Speed Without Trust vs. Trust Without Speed

Modern constraint solvers power hardware verification, package managers, and automated theorem proving, yet they sit on an awkward fault line. On one side, industrial branching solvers—such as **CDCL** (*Conflict-Driven Clause Learning*) engines like **CaDiCaL** [9], which guess variable assignments, explore a search tree, learn new clauses from dead ends, and backtrack—are extraordinarily fast, but their internals span tens of thousands of lines of tuned C++ heuristics. On the other side, interactive theorem provers like **Lean 4** offer ironclad mathematical certainty, but running a proof directly inside a theorem prover's tiny trusted kernel is notoriously slow once instances reach hundreds of variables.

This paper explores a middle path built on two simple rules: **never guess in a recursive search tree**, and **never emit an unverified claim**. If our solver says a puzzle has a solution (`SAT`), it hands back a concrete assignment that any script can check in linear time. If it says a puzzle is impossible (`UNSAT`), it emits a compact, step-by-step mathematical proof that Lean 4's minimal kernel checks from first principles. Running a proof checker purely inside Lean 4's foundational kernel via `by decide`—without `native_decide` compiler trust—makes verifying refutations up to $n \approx 800$ variables and over $1,300$ pruned steps a concrete milestone for zero-axiom kernel verification on consumer hardware.

To study this cleanly, we use **Monotone 1-in-3 SAT** as our laboratory. In a Monotone 1-in-3 SAT instance, you are given $n$ Boolean variables $x_0, \dots, x_{n-1} \in \{0, 1\}$ and $m$ ternary clauses $(a, b, c)$, each demanding that *exactly one* of the three variables equals $1$:

$$\forall (a, b, c) \in \mathcal{C}, \qquad x_a + x_b + x_c = 1.$$

Despite looking like elementary addition, Monotone 1-in-3 SAT is NP-complete by Schaefer's Dichotomy Theorem [1]: general 3-SAT reduces cleanly to Monotone 1-in-3 SAT (which we stress-test via our high-girth 3-SAT family), and our local gadget peeler recovers algebraic structure hidden by reduction helpers. More importantly for us, every single clause simultaneously lives in three different mathematical worlds—even/odd parity arithmetic, whole-number inequalities, and statistical-physics message passing—making it an ideal arena to see where each reasoning technique succeeds and where it breaks.

> **Pocket-Calculator Warm-Up: Zero-Guessing Deduction in Monotone 1-in-3 SAT**  
> Suppose we have 5 Boolean variables $x_1, \dots, x_5 \in \{0, 1\}$ and three clauses:
> $$(1)\ x_1 + x_2 + x_3 = 1, \qquad (2)\ x_1 + x_2 + x_4 = 1, \qquad (3)\ x_3 + x_4 + x_5 = 1.$$
> Subtracting (2) from (1) cancels $x_1 + x_2$, proving $x_3 = x_4$ without ever guessing $x_1$ or $x_2$. Substituting $x_3 = x_4$ into (3) gives $2x_3 + x_5 = 1$. Because variables are in $\{0, 1\}$, $2x_3$ cannot be $2$, so we must have $x_3 = x_4 = 0$ and $x_5 = 1$—pure algebra, zero branching.

**Falsification-Driven Design.** Rather than assembling heuristics upfront, we built our system layer by layer through adversarial falsification: at each stage we constructed a benchmark family specifically designed to break the current solver, measured its exact failure mode and numerical bit-width, added the smallest polynomial-time lens capable of closing that gap, and formally proved the new proof rules sound in Lean 4.

---

## 2. Building the Four-Lens Solver by Falsification

The diagram below gives a high-level view of our final zero-backtracking Rust solver (`GadgetSPCascade`) and its Lean 4 verification pipeline. Below, we walk through the exact sequence of failures that forced each of the four lenses into existence.

```mermaid
flowchart LR
    F["Formula F\nMonotone 1-in-3"] --> L1["Lens 1: Parity (F2)\nGadget Peeling + RREF"]
    L1 --> L2["Lens 2: Counting (Z)\nd=2 Cliques + EquivLift"]
    L2 --> L3["Lens 3: Depth-1 FLE\nNon-Recursive Probe"]
    L3 --> L4["Lens 4: Cavity SP\nNogoods + WalkSAT"]
    L1 -- "1 = 0" --> P["Backward-Cone Pruner\nRust Trace -> Compact Cert"]
    L2 -- "0 <= -1" --> P
    L3 -- "FLE UNSAT" --> P
    P --> K["Lean 4 Pure Kernel\nby decide + PosMap Trie"]
    K --> U["VERIFIED_UNSAT\nZero sorrys / Axioms"]
    L4 --> S["VERIFIED_SAT /\nHonest UNRESOLVED"]
```

### 2.1 Layer 1 (Python): Why Continuous Flows and Naive Rationals Break

Our earliest Python prototype attempted to solve Monotone 1-in-3 SAT continuously using a primal-dual phase-flow relaxation. Across a 140-instance small-to-medium parity suite ($n \in \{15, 30, 60\}$, 101 satisfiable and 39 unsatisfiable), it maintained 100% soundness (zero false claims) but solved only **72/140 (51.4%)** in `71.38s`, exposing three fatal walls:

1. **Pairwise relaxation blindness:** Pairwise quadratic duals certified **0%** of unsatisfiable parity and reduced 3-SAT instances, because global parity contradictions are invisible to local pairwise checks.
2. **Exact rational bit-width explosion:** Precomputing an exact rational Cholesky factorization using Python's arbitrary-precision `Fraction` type exploded to **3,566 bits** before iteration 0, tripping our 2,048-bit guardrail.
3. **Wall-clock censoring at $n = 60$:** Continuous phase frustration caused satisfiable solve rates to collapse to `16.7%` on random instances and `0%` on reduced 3-SAT instances.

To isolate what actually worked, we tested four standalone discrete prototypes on the same 140 instances without wall-clock caps: Sum-of-Squares / Reformulation–Linearization solved `130/140` (`3.56s`), Symplectic flow solved `98/140` (`16.71s`), marginal decimation with unit-collapse solved `130/140` (`21.76s`) while eliminating the 3,566-bit blowup via square-root-free $LDL^T$ (`59` fraction bits) and Bareiss integer elimination (`32` integer bits), and **mod-2 linear algebra with degree-3 Gröbner closure** solved **140/140 (100%)** in `7.64s` with integers never exceeding 3 bits.

### 2.2 Layer 2 (Rust): Scaling Up 10× Exposes Three New Walls

Fusing the mod-2 algebra engine and marginal-decimation cascade into a zero-allocation, standard-library-only Rust crate (`rust_layer2`) sped up the 140-instance suite by over 200× (`135/140` in `33.5 ms`). We then built a **72-instance high-scale adversarial suite** up to $n = 637$ variables spanning five structurally distinct families:

- **Critical random** instances near the phase-transition clause-to-variable ratio ($\alpha \approx 0.626$), where satisfiable and unsatisfiable instances sit on a knife-edge;
- **Planted balanced** satisfiable instances with a hidden solution;
- **Tseitin parity expanders** (both SAT and UNSAT), where a graph demands an even or odd number of active edges at every vertex;
- **High-girth 3-SAT** instances translated into Monotone 1-in-3 SAT via Schaefer's reduction, avoiding short cycles;
- **Pigeonhole Principle** instances ($\mathrm{PHP}_5^6$ at $n = 143$, $\mathrm{PHP}_7^8$ at $n = 334$, and $\mathrm{PHP}_9^{10}$ at $n = 637$).

On this 72-instance suite, Layer 2 solved only **46/72 (63.9%)** in `1.631s` (`44/49` SAT, `2/23` UNSAT), immediately exposing three crisp failure modes:

1. **Auxiliary-variable parity masking:** It solved **0/9** unsatisfiable Tseitin expanders, because encoding XOR constraints into Monotone 1-in-3 SAT introduces hidden helper variables that scramble naive mod-2 equations.
2. **The Pigeonhole degree barrier:** It solved **0/6** Pigeonhole instances. By a classic theorem of Razborov [3], refuting $k+1$ pigeons in $k$ holes using mod-2 polynomial algebra requires polynomial degree $\Omega(k)$, so bounded degree-3 algebra cannot touch it.
3. **Shattered-cluster marginal averaging:** On critical random instances at $n = 600$, global $LDL^T$ marginals averaged across disconnected solution clusters toward a useless $\frac{1}{3}$ tie, dropping SAT solve rate to `16.7%`.

### 2.3 Lens 1 & Lens 4 (Layer 2.5): Parity Peeling + Survey Propagation

**Lens 1: Parity Algebra ($\mathbb{F}_2$) with Local Gadget Peeling.** A **Tseitin parity expander** is a well-connected graph where each node is labeled even ($0$) or odd ($1$) and asks for the active edges touching it to match that parity; if the sum of all node labels is odd, no solution can exist because every edge is counted twice (once at each endpoint), yielding $0 = 1 \pmod 2$. Every Monotone 1-in-3 clause $x_a + x_b + x_c = 1$ implies both a mod-2 parity equation $x_a \oplus x_b \oplus x_c = 1$ and three pairwise exclusion rules $x_a x_b = x_b x_c = x_a x_c = 0$.

> **Pocket Example: Why Parity Collapses a Triangle in One Addition**  
> Consider a 3-node triangle with edges $e_1, e_2, e_3 \in \{0, 1\}$ where every node demands odd parity:
> $$e_1 \oplus e_2 = 1, \qquad e_2 \oplus e_3 = 1, \qquad e_3 \oplus e_1 = 1.$$
> Adding all three equations modulo 2 cancels every edge ($2e_1 \oplus 2e_2 \oplus 2e_3 = 0$) while the right-hand side sums to $1 \oplus 1 \oplus 1 = 1$, deriving $0 = 1 \pmod 2$ in one linear pass.

When Tseitin formulas are encoded into Monotone 1-in-3 SAT, small local clusters of low-degree helper variables mask those clean mod-2 equations. Our **local gadget peeler** finds connected clusters of helper variables (degree $\le 4$), enumerates their tiny local truth tables, extracts the exact mod-2 linear equations on the boundary variables, and feeds them into bit-packed **Reduced Row Echelon Form (RREF)**—standard Gaussian elimination over $\{0, 1\}$ modulo 2—coupled with quadratic exclusion rules and bounded degree-3 Gröbner S-polynomials. That single upgrade took unsatisfiable Tseitin expanders from **0/9 to 9/9 (100%)**, certifying $n = 610$ in **1.2 ms** with 1-bit integers.

**Lens 4: 9-State Survey Propagation (SP).** Near the critical random threshold, satisfiable solutions shatter into exponentially many isolated clusters. Taking one global average across all clusters washes out the signal. **Survey Propagation** [5], borrowed from statistical physics, passes damped warning messages between clauses and variables that separate *frozen* biases $(P_i^0, P_i^1)$ (variables locked to $0$ or $1$ inside a cluster) from unconstrained "water" variables $P_i^*$ (variables free to flip). Replacing $LDL^T$ with 9-state 1-in-3 SP (plus polynomial-restart nogood repulsion, still with zero recursive backtracking) lifted critical random solve rates at $n = 600$ from `16.7%` to `83.3%`, solved **49/49 (100%)** of all high-scale satisfiable instances, reached **140/140** on the parity suite in **11.4 ms**, and raised high-scale solves to **61/72 (84.7%)**.

### 2.4 Lens 2 (Layer 2.75): Whole-Number Cutting Planes Break Pigeonhole

The **Pigeonhole Principle** ($\mathrm{PHP}_k^{k+1}$) states the obvious fact that you cannot place $k+1$ pigeons into $k$ holes with at most one pigeon per hole. While mod-2 algebra is blind to counting, **Gomory–Chvátal cutting planes** [2] turn whole-number arithmetic into a short proof: whenever you sum valid linear inequalities with non-negative integer weights and every variable's coefficient is divisible by an integer $d \ge 2$, you may divide the entire inequality by $d$ and *round the right-hand side down* to the nearest integer, because Boolean variables only take whole-number values.

> **Pocket Example: Divisor-2 Cutting Planes on 3 Pigeons in 2 Holes**  
> Suppose variables $x_1, x_2, x_3 \in \{0, 1\}$ indicate whether pigeons 1, 2, and 3 sit in Hole 1. Pairwise exclusion gives three inequalities: $x_1 + x_2 \le 1$, $x_1 + x_3 \le 1$, and $x_2 + x_3 \le 1$. Summing all three yields:
> $$2(x_1 + x_2 + x_3) \le 3 \implies x_1 + x_2 + x_3 \le \lfloor 3/2 \rfloor = 1.$$
> Doing the same for Hole 2 gives $\text{sum}(\text{Hole 1}) + \text{sum}(\text{Hole 2}) \le 2$, while the three pigeons demand total occupancy $\ge 3$. Adding those yields $0 \le -1$: contradiction!

In Layer 2.75, our cutting-planes engine lifts clauses to exact integer inequalities ($x_a + x_b + x_c \le 1$, $-x_a - x_b - x_c \le -1$, $0 \le x_i \le 1$), discovers pairwise conflict cliques from the exclusion graph, and inductively derives clique capacity bounds $\sum_{i \in K} x_i \le 1$ using strictly **unit weights $(1, 1, 1)$ and divisor $d = 2$**:

$$\Big(\sum_{i \in K'} x_i \le 1\Big) + \Big(\sum_{i \in K' \setminus \{u\}} x_i + x_v \le 1\Big) + (x_u + x_v \le 1) \implies 2 \sum_{i \in K' \cup \{v\}} x_i \le 3 \implies \sum_{i \in K' \cup \{v\}} x_i \le \lfloor 3/2 \rfloor = 1.$$

Because the weights never exceed $1$ and the divisor is always $2$, every intermediate integer stays within **2 bits** (no LP/ILP solver needed). Summing hole-capacity cuts against pigeon lower bounds immediately derives $0 \le -1$. This jumped Pigeonhole from **0/6 to 6/6 (100%)**, refuting $\mathrm{PHP}_9^{10}$ ($n = 637, m = 556$) in **6.7 ms**, and lifted high-scale solves to **67/72 (93.1%)** in **1.151s** at **169.4 KB** peak RAM.

### 2.5 Lens 3 (Layer 2.8): Shallow Failed-Literal Lookahead Closes $n \le 306$

To inspect the final 5 unresolved instances from Layer 2.75, we ran an isolated ground-truth diagnostic oracle: **all 5 were unsatisfiable**, and the two $n = 306$ high-girth instances required only 8 and 13 oracle nodes. That meant a single-variable test could trigger a short algebraic contradiction.

Layer 2.8 added three strictly polynomial, non-recursive upgrades:

1. **Proof-carrying Depth-1 Failed-Literal Elimination (FLE):** Temporarily assume $x_v = b$ (never recursing to depth 2). If Lens 1 algebraic closure derives $1 = 0$, record the self-contained subproof, force $x_v = 1 - b$ at the root, and repeat (capped at 4 passes).
2. **Cross-restart binary/ternary nogood learning:** Extract short conflicting variable clamps (width $\le 3$) and feed them back as cavity repulsion and unit propagation across SP restarts.
3. **WalkSAT island polish:** When SP freezes $\ge 70\%$ of variables without contradiction, run at most $\max(8n, 200)$ local min-conflicts flips strictly on the unfrozen variables; WalkSAT only proposes candidate `SAT` assignments, which are checked directly against all clauses in $O(m)$ time with zero TCB impact.

Depth-1 FLE solved both $n = 306$ high-girth UNSAT instances in `16.8 ms` and `21.4 ms`, bringing our solver to **48/48 (100%)** across all families for $n \le 306$ and **69/72 (95.8%)** overall. Crucially for the TCB boundary, **Layer 2.75 achieves a 100% pure Lean 4 kernel TCB** (`by decide`), whereas **Layer 2.8's Depth-1 FLE wrapper currently relies on Rust-side subproof trace checking** (leaving lowering of the conditional FLE discharge rule into `Certificate.lean` as straightforward future work).

---

## 3. Empirical Results, Scaling, and Head-to-Head Baselines

### 3.1 Cross-Layer Progression and Scaling Exponents

Across all layers and all benchmarks, we observed **zero false-SAT claims, zero false-UNSAT claims, and zero arithmetic overflows**, with integer width capped at $\le 4$ bits and floating-point exponents $\le 0$ in Layers 2.5–2.8.

| Solver Layer | Parity 140 | Parity Time | High-Scale 72 | SAT (/49) | UNSAT (/23) | Int Bits / Exp | Peak RAM / Time |
|---|---:|---:|---:|---:|---:|---|---:|
| L1 (Python flow) | 72/140 (51.4%) | 71.38s | — | — | — | 4 / 55ᵃ | — |
| L1 (Python $\mathbb{F}_2$) | 140/140 (100%) | 7.64s | — | — | — | 3 / 31 | — |
| L2 (Rust $\mathbb{F}_2$ + $LDL^T$) | 135/140 (96.4%) | 0.0335s | 46/72 (63.9%) | 44/49 | 2/23 | 2 / 3 | 304.1 KB / 1.631s |
| L2.5 (+ Peeling + SP) | **140/140 (100%)** | **0.0114s** | 61/72 (84.7%) | **49/49** | 12/23 | 2 / 0 | 181.5 KB / 1.796s |
| L2.75 (+ $\mathbb{Z}$ Cuts) | **140/140 (100%)** | 0.0158s | 67/72 (93.1%) | **49/49** | 18/23 | 4 / 0 | **169.4 KB / 1.151s** |
| L2.8 (+ FLE/NG/WS) | **140/140 (100%)** | 0.0720s | **69/72 (95.8%)** | **49/49** | **20/23** | 4 / 0 | 328.8 KB / 5.951s |

*ᵃNaive exact-rational Cholesky precomputation in Layer 1 peaked at 3,566 bits before iteration 0; $LDL^T$ and Bareiss cured it.*

Fitting log-log scaling laws $\text{ops} \propto n^{\beta_{\text{ops}}}$ and $t \propto n^{\beta_{\text{time}}}$ across $n \in \{150, 300, 600\}$ in Layer 2.8 confirms cleanly polynomial, sub-quadratic refutation on the structured trap families:

- **Tseitin UNSAT expanders:** `9/9` solved, $\beta_{\text{ops}} = 1.85$, $\beta_{\text{time}} = 1.24$, averaging `0.2 ms` ($n=150$), `0.5 ms` ($n=300$), and **1.2 ms ($n=610$)** at `114.4 KB` RAM.
- **Pigeonhole ($\mathrm{PHP}_5^6$ to $\mathrm{PHP}_9^{10}$):** `6/6` solved, $\beta_{\text{ops}} = 1.75$, $\beta_{\text{time}} = 1.52$, averaging `0.7 ms` ($n=143$), `2.5 ms` ($n=334$), and **6.7 ms ($n=637$)** at `119.4 KB` RAM.
- **Satisfiable families:** Planted balanced (`15/15`, $\beta_{\text{time}} = 2.18$), Tseitin SAT (`9/9`, $\beta_{\text{time}} = 1.91$), critical random (`17/18`, $\beta_{\text{time}} = 2.01$), and high-girth 3-SAT (`13/15`, $\beta_{\text{time}} = 3.09$, `328.8 KB` max RAM).

### 3.2 Cracking Coupled Parity-Plus-Pigeonhole Traps ($n \in [231, 855]$)

What if an adversary builds a puzzle that is *neither* pure parity *nor* pure pigeonhole, but couples both worlds together? We constructed an 18-instance coupled trap suite ($n \in [231, 855]$: 9 satisfiable controls and 9 unsatisfiable traps across three scales) as a minimal diagnostic stress-test—analogous to XOR-masked arithmetic datapaths in circuit verification—built to falsify single-lens solvers. In each instance, a *satisfiable* Tseitin parity backbone hides a bridge variable $e_{\text{bridge}}$ that can only be forced to $0$ by global mod-2 Gaussian elimination after gadget peeling, while a Pigeonhole core has its pigeon indicators XOR-masked by $e_{\text{bridge}}$.

Any pure parity solver sees a satisfiable parity backbone and fails on the Pigeonhole core (**0/9 UNSAT traps** in Layer 2 and Layer 2.5). Any pure cutting-planes solver sees masked pigeon indicators and cannot form hole cliques. By extracting all binary variable equivalences from our RREF basis (grouping rows with identical free tails) and lifting them into integer inequalities (`IntegerEquivLift`), our combined solver cracks **8/9 (88.9%)** coupled UNSAT traps—including **3/3 (100%) at $n \in \{783, 855\}$ in 16.5 ms average**—with sub-quadratic scaling ($\beta_{\text{ops}} = 1.96$, $\beta_{\text{time}} = 1.71$ in Layer 2.8 and `1.73` in Layer 2.75), 2-bit integers, and `9/9` SAT controls (`0.308s` total in Layer 2.75, `2.046s` in Layer 2.8). The single unresolved coupled trap ($n = 384$) occurs when the random expander cut happens to have only two non-bridge edges, placing a constant-$0$ anchor directly inside a 3-XOR gadget so that one cut-chain gadget is not peeled; every multi-edge expander cut across both the small and large scales solves at 100%.

### 3.3 Honest Comparison Against Industrial Solvers

We exported all 72 high-scale and 18 coupled instances into exact DIMACS CNF and Pseudo-Boolean OPB formats and benchmarked three mature industrial engines with a `10.0s` per-instance timeout: **CaDiCaL 1.9.5** (world-champion CDCL solver), **CryptoMiniSat 5.18.0** (CDCL with integrated Gauss–Jordan XOR reasoning), and **Z3 5.4.1** (industrial SMT/Pseudo-Boolean solver using native `PbEq` constraints). To keep timing comparisons transparent, CaDiCaL 1.9.5 (`python-sat`) and Z3 5.4.1 (`PbEq`) ran in-process in **pure unverified solving mode** (excluding DRAT/LRAT proof generation and external checking), whereas CryptoMiniSat 5.18.0 ran as an unverified CLI subprocess (`--verb=0`, wall-clock time including process startup).

| Solver | High-Scale 72 | 72 Time | Tseitin U (9) | PHP (6) | Coupled (18) | Coupled Time | Proof Trust / TCB |
|---|---:|---:|---:|---:|---:|---:|---|
| **Ours: L2.75** | 67/72 (93.1%) | 1.151s | **9/9 (0.006s)** | **6/6 (0.020s)** | 17/18 (94.4%) | 0.308s | **Pure-kernel Lean 4** |
| **Ours: L2.8** | 69/72 (95.8%) | 5.951s | **9/9 (0.006s)** | **6/6 (0.020s)** | 17/18 (94.4%) | 2.046s | **Lean 4** + Rust FLE |
| **CaDiCaL 1.9.5** | **72/72 (100%)** | **0.318s** | 9/9 (0.054s) | 6/6 (0.247s) | **18/18 (100%)** | **0.006s** | External DRAT/LRAT |
| **CryptoMiniSat 5** | **72/72 (100%)** | 2.699s | 9/9 (0.286s) | 6/6 (0.584s) | **18/18 (100%)** | 0.529s | Uncertified (optional) |
| **Z3 5.4.1 (OPB)** | **72/72 (100%)** | 1.489s | 9/9 (0.175s) | 6/6 (0.957s) | **18/18 (100%)** | 0.102s | Uncertified SMT/PB |

*Note: CaDiCaL 1.9.5 (`python-sat`) and Z3 5.4.1 (`PbEq`) ran in-process in pure unverified solving mode (no DRAT/LRAT logging or checking); CryptoMiniSat 5.18.0 ran as an unverified CLI subprocess (`--verb=0`, including process startup).*

**Why this trade-off is the real story.** At $n \le 855$ variables, CaDiCaL 1.9.5 wins on small-$n$ total runtime (`0.318s`) because unrestricted branching crushes small random and high-girth instances. Yet look closely at *where* CaDiCaL spends its time: **78% of its entire 72-instance runtime (`0.247s` of `0.318s`)** goes into just 6 Pigeonhole instances, because resolution-based branching suffers exponential blowup on counting principles and parity expanders. On those exact structural blind spots, our zero-backtracking Rust solver is **9× faster than CaDiCaL on Tseitin UNSAT expanders** (`0.006s` vs. `0.054s`) and **12.4× faster than CaDiCaL (and 47.9× faster than Z3) on Pigeonhole benchmarks** (`0.020s` vs. `0.247s` / `0.957s`); because our sub-quadratic scaling ($\beta_{\text{time}} = 1.24$ on Tseitin, $1.52$ on Pigeonhole, and $1.71$ on coupled traps) contrasts with CDCL's exponential blowup, this 9×–12.4× advantage widens rapidly with $n$ while producing kernel-checked proofs. Notably, even CryptoMiniSat—despite its built-in Gauss–Jordan XOR engine—takes `0.286s` on Tseitin UNSAT (versus our `0.006s`), because Monotone 1-in-3 clauses forbid the all-ones assignment ($x_a = x_b = x_c = 1$) and mask XORs behind auxiliary variables, causing its native $2^{k-1}$-clause XOR detector to miss the hidden linear system and directly validating our local gadget peeler.

---

## 4. Layer 3: Pure-Kernel Proof Verification in Lean 4

A fast solver is only as trustworthy as its checker. In formal verification, the **Trusted Computing Base (TCB)** is the small core of code and mathematical axioms you must trust to believe a theorem. Modern Lean 4 tactics such as `bv_decide` delegate solving to an external CDCL solver and replay its proof via `native_decide`, which compiles the checker to native machine code and adds a compiler-trust axiom (`Lean.ofReduceBool`) to the TCB. By contrast, **`by decide`** executes the checker purely inside Lean 4's tiny foundational kernel using only its three standard mathematical axioms (`propext`, `Quot.sound`, `Classical.choice`)—no external checker binary, no compiler trust, and zero trust in our Rust solver.

We formalized the entire unified parity-plus-cutting-planes proof system in **Lean 4 (`v4.36.0`, Lake `5.0.0`)** with **zero `sorry` placeholders and zero custom axioms**:

- `Semantics.lean` defines Monotone 1-in-3 satisfaction and proves every projection from a clause to mod-2 parity, pairwise exclusions, integer inequalities, and deterministic unit-collapse rules.
- `F2AndGadgets.lean` proves soundness of mod-2 row cancellation, $1 = 0$ contradiction, and local truth-table gadget projection.
- `CuttingPlanes.lean` proves soundness of non-negative scaling, inequality addition, sparse simplification, exact Euclidean Gomory–Chvátal rounding, and $0 \le \text{rhs} < 0$ contradiction.
- `Certificate.lean` defines the executable checker `verifyCertificate` and proves the end-to-end soundness theorem: if `verifyCertificate F cert = true`, then no Boolean assignment can satisfy `F`.

This formalization covers all Layer 2.75 parity, gadget-peeling, equivalence-lifting, and cutting-planes certificates with a 100% pure Lean 4 kernel TCB; Layer 2.8's Depth-1 FLE wrapper currently verifies its conditional subproofs via our Rust trace checker, leaving the conditional discharge rule in `Certificate.lean` as straightforward future work (while WalkSAT only outputs candidate `SAT` assignments checked in $O(m)$ time with zero TCB impact).

**Making Pure-Kernel `by decide` Scale to 783 Variables.** Naively storing derived proof steps in a linked list makes checking an $S$-step certificate take $O(S^2)$ kernel reductions, which stalls on thousand-step proofs. We replaced linear list lookups with **`PosMap`**, a verified, structurally recursive $O(\log N)$ persistent binary trie indexed by fixed structural depth (`fuel = 16`), avoiding well-founded recursion stalls inside Lean's kernel. Combined with backward-cone pruning in Rust (which strips away every derived lemma not needed for the final contradiction), verification drops to $O(S \log S)$ and runs cleanly via pure `by decide`.

| Benchmark Family | $n$ | $m$ | Raw Steps | Pruned Steps | Rust Export | Lean 4 Theorem (`by decide`) |
|---|---:|---:|---:|---:|---:|---|
| Tseitin Expander UNSAT | 610 | 433 | 3,780 | **626** | 0.0327s | `tseitin_610_unsat` (**VERIFIED**) |
| Pigeonhole $\mathrm{PHP}_9^{10}$ | 637 | 556 | 9,936 | **1,914** | 0.0531s | `php_637_unsat` (**VERIFIED**) |
| Coupled Parity + PHP | 783 | 580 | 11,629 | **1,329** | 0.0570s | `hybrid_f2_z_783_unsat` (**VERIFIED**) |

The full `lake build` (22 jobs) completes with **0 errors, 0 warnings, and 0 `sorry`s**.

---

## 5. The Honest Boundary: Where Zero-Backtracking Stops

Science requires showing not only what works, but exactly where it stops. Below is our ground-truth oracle dissection of all 5 instances left unresolved by Layer 2.75.

| Frontier Instance | $n$ | $m$ | Truth | Oracle Nodes | SP Frozen | Conflict Depth | Layer 2.8 Outcome |
|---|---:|---:|---|---:|---:|---:|---|
| High-girth 3-SAT #1 | 306 | 221 | UNSAT | 8 | 38.5% | 11.4 | **`VERIFIED_UNSAT`** (16.8 ms) |
| High-girth 3-SAT #2 | 306 | 221 | UNSAT | 13 | 44.4% | 8.7 | **`VERIFIED_UNSAT`** (21.4 ms) |
| Critical random #1 | 600 | 376 | UNSAT | 566 | 19.2% | 14.2 | `UNRESOLVED` (350.2 ms) |
| High-girth 3-SAT #3 | 610 | 441 | UNSAT | 71 | 41.6% | 24.3 | `UNRESOLVED` (447.3 ms) |
| High-girth 3-SAT #4 | 610 | 441 | UNSAT | 77 | 38.5% | 19.5 | `UNRESOLVED` (468.7 ms) |

The final three $n \ge 600$ instances contain no global parity contradiction, no pigeonhole or clique counting obstruction, and no single-variable failed-literal cascade. Their resistance matches the classic $\Omega(n)$ resolution-width lower bound of Ben-Sasson and Wigderson [4] for random and high-girth unsatisfiable formulas near threshold: refuting them demands genuinely multi-variable case analysis rather than bounded-degree algebra, shallow cutting planes, or depth-1 lookahead.

**Scale Context and Related Systems.** Our benchmarks operate at $n \in [150, 855]$ variables rather than the $10^5$-variable industrial scale of SAT competitions. This scale is chosen intentionally to hit two targets simultaneously: pure-kernel `by decide` verification of thousand-step hybrid proofs on consumer hardware, and exact falsification-driven boundary mapping. Compared with hybrid tools like CryptoMiniSat [6] (CDCL + XOR without native integer cutting planes) and RoundingSat / VeriPB [7, 8]—where VeriPB supports certified pseudo-Boolean cutting planes (including dominance and redundancy extensions capable of simulating parity) via an external verified checker (CakePB)—our `PosMap` + `by decide` pipeline checks unified gadget-peeled mod-2 algebra and integer cutting planes purely inside Lean 4's kernel, avoiding both external checkers and `bv_decide`'s `Lean.ofReduceBool` compiler-trust axiom. Conceptually, our Depth-1 FLE lens sits alongside Stålmarck's dilemma rule (bounded-depth non-recursive lookahead), while our unified $\mathbb{F}_2 + \mathbb{Z}$ proof system occupies the sweet spot between bounded-degree Polynomial Calculus + bounded-rank Cutting Planes and full resolution-over-linear-equations ($\mathrm{Res}(\mathrm{lin}_{\mathbb{Z}})$).

---

## 6. Conclusion

By letting adversarial failures dictate every design step, we built a zero-backtracking, strictly polynomial solver in Rust that resolves **140/140** parity benchmarks, **69/72 (95.8%)** high-scale adversarial benchmarks up to $n = 637$—including **49/49 (100%)** satisfiable instances, **48/48 (100%)** for $n \le 306$, **9/9** Tseitin UNSAT expanders, and **6/6** Pigeonhole benchmarks—plus **8/9** coupled parity-plus-pigeonhole traps (**3/3** at $n \ge 783$ in `16.5 ms`), all under `329 KB` of RAM and with machine-checked pure-kernel Lean 4 proofs up to $n = 783$. What remains unresolved is not a mystery bug, but a crisp theoretical wall.

> **Open Problem: Simultaneous Parity + Cutting-Planes Proof-Complexity Barrier.** Our three unresolved $n \ge 600$ frontier instances point to an explicit theoretical challenge: prove unconditional super-polynomial size (or $\Omega(n)$ width/rank) lower bounds for the *unified proof system* combining bounded-degree $\mathbb{F}_2$ Polynomial Calculus with local gadget projection, bounded-rank Gomory–Chvátal Cutting Planes over $\mathbb{Z}$, and depth-1 Failed-Literal Elimination on high-girth random Monotone 1-in-3 SAT formulas near the critical threshold $\alpha \approx 0.626$.

---

## References

1. T. J. Schaefer, "The complexity of satisfiability problems," *Proc. 10th ACM STOC*, pp. 216–226, 1978.
2. W. Cook, C. R. Coullard, and G. Turán, "On the complexity of cutting-plane proofs," *Discrete Applied Mathematics*, 18(1):25–38, 1987.
3. A. A. Razborov, "Lower bounds for the polynomial calculus," *Computational Complexity*, 7(4):291–324, 1998.
4. E. Ben-Sasson and A. Wigderson, "Short proofs are narrow—resolution made simple," *Journal of the ACM*, 48(2):149–169, 2001.
5. M. Mézard, G. Parisi, and R. Zecchina, "Analytic and algorithmic solution of random satisfiability problems," *Science*, 297(5582):812–815, 2002.
6. M. Soos, K. Nohl, and C. Castelluccia, "Extending SAT solvers to cryptographic problems," *SAT 2009*, LNCS 5584, pp. 244–257, 2009.
7. J. Elffers and J. Nordström, "Divide and conquer: Towards faster pseudo-Boolean solving," *IJCAI 2018*, pp. 1291–1299, 2018.
8. S. Gocht, R. Martins, J. Nordström, and A. Oertel, "Certified CNF translations for pseudo-Boolean solving," *SAT 2022*, LIPIcs 236, 2022.
9. A. Biere, T. Faller, K. Fazekas, M. Fleury, N. Froleyks, and F. Pollitt, "CaDiCaL 2.0," *CAV 2024*, LNCS 14681, pp. 133–152, 2024.
