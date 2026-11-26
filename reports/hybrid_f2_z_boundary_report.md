# Coupled Hybrid ($\mathbb{F}_2$ Parity $\oplus$ $\mathbb{Z}$ Pigeonhole) Boundary Experiment (`F6_hybrid_f2_z_trap`)

## 1. Experimental Hypothesis & Construction

To test whether simultaneous $\mathbb{F}_2$ parity and $\mathbb{Z}$ counting obstructions collapse in polynomial time or expose a cross-system coupling barrier, we implemented `gen_f6_hybrid_f2_z_trap` in `rust_layer2/src/generators.rs` across 18 instances (`3` UNSAT coupled traps + `3` SAT decoupled controls at each target scale $n \in \{150, 300, 600\}$, actual $n \in [231, 855]$):

1. **Satisfiable $\mathbb{F}_2$ Parity Backbone:** A connected 3-regular expander Tseitin XOR system ($v \in \{6, 10, 18\}$ vertices) reduced via Schaefer 3-XOR gadgets, augmented with a global cut-chain over a balanced vertex cut $S$ ($|S| = v/2$) encoding $\bigoplus_{e \in \delta(S) \setminus \{e_{\text{bridge}}\}} e = \bigoplus_{v \in S} c_v$. The backbone is **100% satisfiable** (so $\mathbb{F}_2$ alone cannot refute it), and **only** global $\mathbb{F}_2$ RREF after peeling $v/2$ expander gadgets derives $e_{\text{bridge}} = 0$.
2. **XOR-Masked $\mathbb{Z}$ Pigeonhole Core:** A Pigeonhole system ($\text{PHP}_k^{k+1}$ for UNSAT traps; $\text{PHP}_k^k$ for SAT controls, $k \in \{3, 4, 5\}$) whose hole at-most-one clauses act on $p_{i,j}$ while pigeon carry chains ($\sum_j q_{i,j} = 1$) act on XOR-masked indicators linked via `add_3xor(p_{i,j}, q_{i,j}, e_bridge, 0)`. Thus raw $\mathbb{Z}$ cutting planes sees disconnected cliques and lower bounds until $\mathbb{F}_2$ RREF derives $e_{\text{bridge}} = 0$ and transfers $q_{i,j} = p_{i,j}$ into $\mathbb{Z}$.

## 2. Cross-Lens $\mathbb{F}_2 \leftrightarrow \mathbb{Z}$ Bridge (`IntegerEquivLift`)

Two general proof-carrying upgrades closed the coupling:
1. **Complete RREF Free-Tail Equivalence Extraction (`cutting_planes.rs`):** Extracts **all** binary equalities $x_u \oplus x_v = 0$ implied by RREF—both direct 2-bit `rhs == 0` rows and pairs of multi-bit pivot rows sharing an identical `(free_tail, rhs)` signature via `ProofStep::F2Xor`—lifting each into exact $\mathbb{Z}$ inequalities $x_u - x_v \le 0$ and $x_v - x_u \le 0$ (`ProofStep::IntegerEquivLift`).
2. **Alternating $\mathbb{F}_2 \leftrightarrow \mathbb{Z}$ Fixpoint & Permutation-Invariant Cliques (`solver_v25.rs`, `cutting_planes.rs`):** Runs a bounded fixpoint loop between gadget peeling/RREF and cutting planes, selecting maximal conflict cliques in descending size order so hole cliques always beat smaller gadget triangles.

## 3. Empirical Results (18 Instances, $n \in [231, 855]$)

### 3.1 Cross-Layer Summary (`f6_hybrid_results.csv`)

| Solver Layer | `F6` SAT Controls (/9) | `F6` UNSAT Traps (/9) | `UNRESOLVED` | `FALSE_SAT` / `FALSE_UNSAT` / `OVERFLOW` | Max Int Bits | Peak Mem (KB) | Total Time (s) |
|---|---:|---:|---:|---:|---:|---:|---:|
| **Layer 2 (`HybridGroebner`)** | 9/9 (100%) | **0/9 (0.0%)** | 9 | 0 / 0 / 0 | 2 | 415.2 | 0.5977 |
| **Layer 2.5 (`GadgetSP`, $\mathbb{F}_2$ only)** | 9/9 (100%) | **0/9 (0.0%)** | 9 | 0 / 0 / 0 | 2 | 291.6 | 1.8271 |
| **Layer 2.75 (`+ Z-CP + EquivLift`)** | **9/9 (100%)** | **8/9 (88.9%)** | 1 | **0 / 0 / 0** | **2** | **253.9** | **0.3081** |
| **Layer 2.8 (`+ FLE/NG/WS`)** | **9/9 (100%)** | **8/9 (88.9%)** | 1 | **0 / 0 / 0** | **2** | 467.0 | 2.0455 |

### 3.2 Scaling Exponents ($\beta$) on Coupled $\mathbb{F}_2 \oplus \mathbb{Z}$ Instances

| Subfamily | Target $n$ | Avg $n$ | Layer 2.75 / 2.8 Solved | Avg Solve Time (s) | Avg Ops | $\beta_{\text{ops}}$ | $\beta_{\text{time}}$ |
|---|---:|---:|---:|---:|---:|---:|---:|
| `F6_hybrid_f2_z_unsat` | 150 | 264 | **3/3 (100%)** | 0.0024 | 32,241 | **1.96** | **1.73** (L2.75) / **1.71** (L2.8) |
| `F6_hybrid_f2_z_unsat` | 300 | 419 | 2/3 (66.7%) | 0.0050 | 72,504 | 〃 | 〃 |
| `F6_hybrid_f2_z_unsat` | 600 | 807 | **3/3 (100%)** | **0.0165** | 283,694 | 〃 | 〃 |
| `F6_hybrid_f2_z_sat` | 150 | 231 | **3/3 (100%)** | 0.0037 | 804,494 | **1.97** | **1.82** (L2.75) / **2.07** (L2.8) |
| `F6_hybrid_f2_z_sat` | 300 | 382 | **3/3 (100%)** | 0.0093 | 2,102,420 | 〃 | 〃 |
| `F6_hybrid_f2_z_sat` | 600 | 745 | **3/3 (100%)** | 0.0313 | 8,044,739 | 〃 | 〃 |

- **Sharp Separation:** Single-lens solvers (Layer 2 and Layer 2.5, $\mathbb{F}_2$ only) score **`0/9` (`0.0%`)** on the coupled UNSAT traps, while the unified $\mathbb{F}_2 \leftrightarrow \mathbb{Z}$ fixpoint collapses **`8/9` (`88.9%`)**—including **`3/3` (`100%`) at $n \in \{783, 855\}$** in **`16.5 ms`** average with **sub-quadratic scaling** ($\beta_{\text{time}} = 1.71$) and **`max_int_bits = 2`**.
- **Single Unresolved Edge Case (`t300_s20270206`, $n = 384$):** Occurs when the random expander cut has $|\delta(S) \setminus \{e_{\text{bridge}}\}| = 2$, placing `const_0` directly inside a 3-XOR gadget so one cut-chain gadget is not peeled; all multi-edge expander cuts (`t150` and `t600`) solve at `100%`.

## 4. Machine-Checked Lean 4 Pure-Kernel Verification ($n = 783$)

We extended `lean4_layer3/Monotone1in3Layer3/Certificate.lean` with verified `.integerEquivLift`, `.unitOneForcesZero`, and `.unitTwoZerosForceOne` rules (zero `sorry`s), exported `F6_hybrid_f2_z_unsat_trap_t600_s20274242` via `cargo run --release -- --export-f6-cert`, and pure-kernel verified (`by decide`) `hybrid_f2_z_783_unsat` in `VerifyBridge.lean`:

- **Instance:** `F6_hybrid_f2_z_unsat_trap_t600_s20274242` ($n = 783, m = 580$)
- **Certificate:** `HybridF2Z600Cert.lean` — `11,629` raw Rust steps $\to$ **`1,329` backward-cone pruned steps** (`0.0570s` solve + export)
- **Lean 4 Build (`lake build`):** **`Build completed successfully (22 jobs)`**, 0 errors, 0 warnings, 0 `sorry`s, pure kernel reduction (`by decide`, no `native_decide`).
