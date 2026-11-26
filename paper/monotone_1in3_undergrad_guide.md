# Building a Solver That Cannot Lie: From Light-Switch Puzzles to Kernel-Verified Proofs in Lean 4

*An Undergraduate and Software Engineer's Guide to Multi-Lens Constraint Solving and Formal Verification*

**Miguel Gutierrez** — Independent Researcher (`miguelgutierrezbarcelo@gmail.com`)  
**Code & Lean 4 Artifacts:** https://github.com/its-miguel/dont-lie

---

## Abstract

How do you build a constraint solver that can crack 600-variable NP-complete puzzles in milliseconds *without* brute-force guessing—and prove mathematically that it can never lie? This companion paper walks through our **Monotone 1-in-3 SAT** solver from first principles. Starting from a 4-switch puzzle you can solve by hand in 30 seconds, we build a strictly polynomial, zero-backtracking Rust solver (`GadgetSPCascade`) out of four complementary reasoning lenses: even/odd parity algebra ($\mathbb{F}_2$) with local gadget peeling, whole-number cutting planes ($\mathbb{Z}$), statistical-physics Survey Propagation, and depth-1 Failed-Literal Elimination. Across 140 small-to-medium instances, our solver resolves **140/140 (100%)**; across 72 high-scale adversarial benchmarks up to $n = 637$, it resolves **69/72 (95.8%)**—including **49/49 (100%)** of all satisfiable instances and **48/48 (100%)** for $n \le 306$—with zero false claims, $\le 4$-bit integers, and under `329 KB` of RAM. On structured parity and pigeonhole traps, it runs **9× to 12.4× faster than CaDiCaL 1.9.5**, while verifying its unsatisfiability proofs purely inside **Lean 4's minimal kernel** (`by decide`) up to $n = 783$ variables.

---

## 1. A 30-Second Puzzle: What Is Monotone 1-in-3 SAT?

Imagine a wall with $n$ light switches. Each switch $x_i$ is either **OFF (`0`)** or **ON (`1`)**. Every rule (clause) points to three switches $(a, b, c)$ and demands:

$$x_a + x_b + x_c = 1.$$

In plain English: **exactly ONE of these three switches must be ON**—never zero, never two, never three. Despite looking like elementary arithmetic, **Monotone 1-in-3 SAT** is **NP-complete**: any other NP-complete problem can be translated into a wall of these light switches.

> **Try It Yourself (4 Switches, 2 Rules):**
> - Rule 1: $x_1 + x_2 + x_3 = 1$
> - Rule 2: $x_1 + x_2 + x_4 = 1$
>
> Without guessing $x_1$ or $x_2$, subtract Rule 2 from Rule 1: the $x_1 + x_2$ cancels out, proving **$x_3 = x_4$**! If we add Rule 3 ($x_3 + x_4 + x_5 = 1$), then since $x_3 = x_4 \in \{0, 1\}$, they cannot both be $1$ (their sum would be $2 > 1$), forcing $x_3 = 0, x_4 = 0, x_5 = 1$ with **zero guessing**.

At $n = 600$ switches, there are $2^{600}$ combinations—more than atoms in the observable universe. Brute-force guessing fails on impossible (`UNSAT`) walls because you would have to rule out every combination. Our goal: **push strictly polynomial, zero-backtracking deduction as far as possible, and prove mathematically that the solver can never lie.**

---

## 2. Why One Trick Never Beats Every Lock: The Four Lenses

Every lens in `GadgetSPCascade` was added only after we constructed an adversarial benchmark that broke the previous layer.

### Lens 1: Even/Odd Parity Loops ($\mathbb{F}_2$) and Gadget Peeling
Every 1-in-3 rule implies that $x_a \oplus x_b \oplus x_c = 1 \pmod 2$. On a 3-node parity triangle:
$$e_1 \oplus e_2 = 1, \qquad e_2 \oplus e_3 = 1, \qquad e_3 \oplus e_1 = 1,$$
adding all three equations modulo 2 cancels every variable ($x \oplus x = 0$) and leaves **$0 = 1 \pmod 2$**—an instant contradiction!

- **The Catch (Helper-Variable "Sunglasses"):** Real Tseitin expander benchmarks encode XOR rules into Monotone 1-in-3 SAT using extra local helper switches that blind raw $\mathbb{F}_2$ Gaussian elimination (Layer 2 scored **0/9**).
- **The Fix (`Gadget Peeling`, Layer 2.5):** Detect low-degree ($\le 4$) local clusters, evaluate exact local truth tables, and project out hidden $\mathbb{F}_2$ affine invariants. Tseitin UNSAT expanders jumped from **0% to 100% (9/9)**, refuting an $n = 610$ expander in **1.2 ms** with 1-bit integers.

### Lens 2: Whole-Number Counting ($\mathbb{Z}$ Cutting Planes)
Now try **3 pigeons in 2 birdhouses** ($x_{p,h} = 1$ if pigeon $p$ sleeps in hole $h$). Every pigeon picks a hole ($x_{p,1} + x_{p,2} = 1$, sum $= 3$), and no two pigeons share Hole 1:
$$x_{1,1} + x_{2,1} \le 1, \qquad x_{1,1} + x_{3,1} \le 1, \qquad x_{2,1} + x_{3,1} \le 1.$$

- **Why Lens 1 Goes Blind:** Setting all $x_{p,1} = 1, x_{p,2} = 0$ satisfies $x_{p,1} \oplus x_{p,2} = 1 \pmod 2$! Even/odd arithmetic cannot count to 3 (Razborov's $\Omega(k)$ degree lower bound; Layer 2.5 scored **0/6** on Pigeonhole).
- **The Fix (Divisor-2 Gomory–Chvátal Rounding, Layer 2.75):** Sum the three pairwise conflicts for Hole 1 with unit weights $(1, 1, 1)$:
  $$2(x_{1,1} + x_{2,1} + x_{3,1}) \le 3 \implies x_{1,1} + x_{2,1} + x_{3,1} \le \lfloor 3/2 \rfloor = 1.$$
  Repeating for Hole 2 gives total capacity $\le 2$ against 3 pigeons ($\ge 3$), deriving **$0 \le -1$** with **2-bit coefficients**. Pigeonhole jumped from **0% to 100% (6/6)**, refuting $\text{PHP}_9^{10}$ ($n = 637$) in **6.7 ms**.

### Lens 3: Navigating Solution Islands (9-State Survey Propagation + WalkSAT)
Near the critical ratio ($\alpha \approx 0.626$), satisfiable random instances shatter into disconnected solution "islands." Global averages ($LDL^\top$) average across islands and point straight into the ocean (Layer 2 scored **16.7%** at $n = 600$).

Our **9-state 1-in-3 Survey Propagation (SP)** separates *frozen* island variables $(P_i^0, P_i^1)$ from unconstrained *water* variables $P_i^*$. Once SP freezes $\ge 70\%$ of variables, bounded $O(n)$ **WalkSAT island polish** ($\le \max(8n, 200)$ flips) snaps the remaining water variables into an exact solution—solving **49/49 (100%)** of all satisfiable high-scale instances.

### Lens 4: Depth-1 Lookahead and Coupled $\mathbb{F}_2 \leftrightarrow \mathbb{Z}$ Synthesis
- **Depth-1 Failed-Literal Elimination (`FLE`, Layer 2.8):** Tests $x_v = 0$ (or $1$) for one non-recursive pass; if closure hits $1 = 0$, it forces the opposite value with a self-contained proof. This closed both remaining $n = 306$ frontier seeds in **16.8–21.4 ms**, reaching **48/48 (100%)** for $n \le 306$.
- **Coupled `F6` Traps ($n \in [231, 855]$):** Locking a Pigeonhole core behind a satisfiable Tseitin parity mask defeats single-lens $\mathbb{F}_2$ solvers completely (**0/9** UNSAT traps). Grouping RREF pivot rows by their free-tail signatures to recover *all* implied binary equalities and lifting them into $\mathbb{Z}$ via `IntegerEquivLift` collapses **8/9 (88.9%)** of the UNSAT traps—including **3/3 (100%)** at $n \in \{783, 855\}$ in **16.5 ms** average ($\beta_{\text{time}} = 1.71$, 2-bit integers)—plus **9/9 (100%)** SAT controls.

---

## 3. Audited Results, External Baselines, and the Honest Frontier

| Solver / Layer | Parity (/140) | High-Scale (/72) | Tseitin UNSAT (9) | Pigeonhole (6) | Coupled `F6` (/18) | Peak Mem | Certification / TCB |
|---|---:|---:|---:|---:|---:|---:|---|
| L1 Python (`PD-PFGC`) | 72 (51.4%) | — | — | — | — | — | Python verifier (3,566-bit blowup) |
| L2 Rust (`HybridGroebner`) | 135 (96.4%) | 46 (63.9%) | 0/9 | 0/6 | 9/18 (0/9 U) | 304.1 KB | Rust checker |
| L2.5 Rust (`GadgetSP`) | **140 (100%)** | 61 (84.7%) | **9/9 (1.2 ms)** | 0/6 | 9/18 (0/9 U) | 181.5 KB | Rust checker |
| L2.75 Rust (`+ Z-CP`) | **140 (100%)** | 67 (93.1%) | **9/9 (0.006s)** | **6/6 (0.020s)** | 17/18 (8/9 U) | **169.4 KB** | **Pure-kernel Lean 4 (`by decide`)** |
| L2.8 Rust (`+ FLE/NG/WS`) | **140 (100%)** | **69 (95.8%)** | **9/9 (0.006s)** | **6/6 (0.020s)** | 17/18 (8/9 U) | 328.8 KB | **Pure-kernel Lean 4** + Rust |
| `CaDiCaL 1.9.5` (CNF) | — | **72 (100%)** | 9/9 (0.054s) | 6/6 (0.247s) | **18/18** (0.006s) | — | External LRAT/DRAT (uncertified here) |
| `CryptoMiniSat 5.18` (CNF) | — | **72 (100%)** | 9/9 (0.286s) | 6/6 (0.584s) | **18/18** (0.529s) | — | Uncertified (FRAT optional) |
| `Z3 5.4.1` (`PbEq` OPB) | — | **72 (100%)** | 9/9 (0.175s) | 6/6 (0.957s) | **18/18** (0.102s) | — | Uncertified SMT/PB |

Across all our layers: `FALSE_SAT = FALSE_UNSAT = OVERFLOW = 0`, `max_int_bits <= 4`, and `max_float_exp <= 0` (Layers 2.5–2.8). While industrial CDCL (`CaDiCaL 1.9.5`) solves 72/72 faster overall (`0.318s` vs. `1.151s` for L2.75) via unrestricted branching, our zero-backtracking solver is **9× faster than CaDiCaL on Tseitin UNSAT** and **12.4× faster than CaDiCaL / 47.9× faster than Z3 on Pigeonhole** (where CaDiCaL spends **78%** of its entire 72-instance runtime).

Only **3 out of 72** high-scale instances remain unresolved (`F1_n600_s20310565`, `F4_t600_s20328727`, `F4_t600_s20329736`)—all unstructured `UNSAT` instances at $n \ge 600$ marking the classical $\Omega(n)$ resolution-width barrier.

---

## 4. Why Rust and Lean 4 Matter in Real-World Software Engineering

- **Rust's Hardware & Type Discipline:** Bit-packing 64 variables into a `u64` makes $\mathbb{F}_2$ elimination hardware XOR (`^`). Deterministic `BitLedger` guardrails enforce `max_int_bits <= 4` and `< 329 KB` peak RAM, while Rust's algebraic `enum ProofStep` prevents malformed proof traces at compile time.
- **Pure-Kernel Lean 4 (`by decide` vs. `native_decide`):** `native_decide` compiles the checker to native code, silently trusting the compiler (`Lean.ofReduceBool`). We proved `unified_certificate_sound` in Lean `v4.36.0` (zero `sorry`s, zero custom axioms) and check real certificates via **pure kernel reduction (`by decide`)**, keeping the TCB strictly to Lean's foundational axioms (`propext`, `Quot.sound`, `Classical.choice`).
- **Fast Kernel Checking:** Backward-cone pruning strips dead exploratory lemmas, and a verified $O(\log N)$ persistent binary trie (`PosMap`, structural `fuel = 16`) cuts kernel checking from $O(S^2)$ to $O(S \log S)$.

| Lean 4 Module | Benchmark Family | $n$ | $m$ | Raw $\to$ Pruned Steps | Rust Export | Kernel Theorem (`by decide`) |
|---|---|---:|---:|---:|---:|---|
| `Tseitin610Cert` | Tseitin Expander | 610 | 433 | `3,780 -> 626` | `0.0327s` | `tseitin_610_unsat` (**VERIFIED**) |
| `Pigeonhole637Cert` | Pigeonhole ($\text{PHP}_9^{10}$) | 637 | 556 | `9,936 -> 1,914` | `0.0531s` | `php_637_unsat` (**VERIFIED**) |
| `HybridF2Z600Cert` | Coupled $\mathbb{F}_2 \oplus \mathbb{Z}$ (`F6`) | 783 | 580 | `11,629 -> 1,329` | `0.0570s` | `hybrid_f2_z_783_unsat` (**VERIFIED**) |

The full `lake build` (`22 jobs`) completes with **0 errors, 0 warnings, and 0 `sorry`s**.
