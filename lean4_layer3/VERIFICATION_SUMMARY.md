# Layer 3 (Lean 4) Verification Summary — Unified $\mathbb{F}_2 + \mathbb{Z}$ Monotone 1-in-3 SAT Proof System

> **Build Status:** **VERIFIED — `Build completed successfully (22 jobs)`** under `Lean 4.36.0` (`Lake 5.0.0`, `arm64-apple-darwin24.6.0`), with **zero errors, zero warnings, zero `sorry` placeholders, and zero custom axioms** (pure kernel reduction `by decide`, no `native_decide` / `Lean.ofReduceBool`).

---

## 1. Module & Theorem Inventory (1-to-1 Mapping to `rust_layer2/src/verifier.rs`)

### `Monotone1in3Layer3/Semantics.lean`
| Lean 4 Theorem | Exact Signature | Rust `verifier.rs` Mapping |
|---|---|---|
| `clause_f2_parity` | `Clause1in3 x a b c → (bit (x a) + bit (x b) + bit (x c)) % 2 = 1` | `ProofStep::ClauseF2Axiom` |
| `clause_f2_xor` | `Clause1in3 x a b c → xor (xor (x a) (x b)) (x c) = true` | `ProofStep::ClauseF2Axiom` |
| `clause_annihilator_ab` / `_bc` / `_ac` | `Clause1in3 x a b c → bit (x a) * bit (x b) = 0` | `ProofStep::ClauseAnnihilator` |
| `clause_dup_literal_zero` | `Clause1in3 x a a b → x a = false` | `ProofStep::DupLiteralZero` |
| `clause_triple_literal_false` | `Clause1in3 x a a a → False` | `ProofStep::TripleLiteralContradiction` |
| `clause_z_upper` | `Clause1in3 x a b c → bitInt (x a) + bitInt (x b) + bitInt (x c) ≤ 1` | `ProofStep::IntegerClauseLift { is_upper: true }` |
| `clause_z_lower` | `Clause1in3 x a b c → -(bitInt (x a)) - bitInt (x b) - bitInt (x c) ≤ -1` | `ProofStep::IntegerClauseLift { is_upper: false }` |
| `unit_collapse_true` | `Clause1in3 x a b c → x a = true → x b = false ∧ x c = false` | `ProofStep::UnitOneForcesZero` |
| `unit_collapse_two_false` | `Clause1in3 x a b c → x a = false → x b = false → x c = true` | `ProofStep::UnitTwoZerosForceOne` |
| `unit_all_false_contradiction` | `Clause1in3 x a b c → x a = false → x b = false → x c = false → False` | `ProofStep::UnitAllZeroContradiction` |
| `unit_two_true_contradiction` | `Clause1in3 x a b c → x a = true → x b = true → False` | `ProofStep::UnitTwoOnesContradiction` |

### `Monotone1in3Layer3/F2AndGadgets.lean`
| Lean 4 Theorem | Exact Signature | Rust `verifier.rs` Mapping |
|---|---|---|
| `f2_xor_combine_sound` | `SatisfiesF2 x c1 → SatisfiesF2 x c2 → SatisfiesF2 x ⟨c1.vars ++ c2.vars, xor c1.rhs c2.rhs⟩` | `ProofStep::F2Xor` |
| `f2_xor_reduce_sound` | `SatisfiesF2 x c1 → SatisfiesF2 x c2 → SatisfiesF2 x ⟨f2XorReduce c1.vars c2.vars, xor c1.rhs c2.rhs⟩` | `ProofStep::F2Xor` (mod-2 cancellation) |
| `f2_contradiction_sound` | `SatisfiesF2 x ⟨[], true⟩ → False` | `LinEq::is_contradiction` (`0 = 1 mod 2`) |
| `clause_to_f2_sound` | `Clause1in3 x a b c → SatisfiesF2 x ⟨f2XorReduce [a, b] [c], true⟩` | `ProofStep::ClauseF2Axiom` |
| `local_cluster_f2_sound` | `(F : Formula1in3) → (ax : LocalClusterF2Axiom F) → SatisfiesFormula F x → SatisfiesF2 x ax.eq` | `ProofStep::LocalClusterF2Axiom` |

### `Monotone1in3Layer3/CuttingPlanes.lean`
| Lean 4 Theorem | Exact Signature | Rust `verifier.rs` Mapping |
|---|---|---|
| `scale_ineq_sound` | `0 ≤ lam → SatisfiesIntIneq x ineq → SatisfiesIntIneq x (scaleIneq lam ineq)` | `ProofStep::IntegerCut` (`multipliers[k] >= 0`) |
| `add_ineq_sound` | `SatisfiesIntIneq x i1 → SatisfiesIntIneq x i2 → SatisfiesIntIneq x (addIneq i1 i2)` | `ProofStep::IntegerCut` row summation |
| `lin_comb_sound` | `(∀ t ∈ terms, 0 ≤ t.1) → (∀ t ∈ terms, SatisfiesIntIneq x t.2) → SatisfiesIntIneq x (linComb terms)` | `ProofStep::IntegerCut` linear combination |
| `simplify_ineq_sound` | `SatisfiesIntIneq x ineq → SatisfiesIntIneq x ⟨simplifyCoeffs ineq.coeffs, ineq.rhs⟩` | `BTreeMap` coefficient aggregation & zero drop |
| `gomory_chvatal_cut_sound` | `0 < d → (∀ p ∈ ineq.coeffs, p.1 % d = 0) → SatisfiesIntIneq x ineq → SatisfiesIntIneq x ⟨ineq.coeffs.map (fun (c, v) => (c / d, v)), ineq.rhs / d⟩` | `ProofStep::IntegerCut` (`% d == 0`, `div_euclid(d)`) |
| `integer_contradiction_sound` | `SatisfiesIntIneq x ⟨[], rhs⟩ → rhs < 0 → False` | `ProofStep::IntegerContradiction` (`0 ≤ -1`) |
| `clause_lift_upper_sound` / `_lower_sound` | `Clause1in3 x a b c → SatisfiesIntIneq x ...` | `ProofStep::IntegerClauseLift` |
| `box_upper_sound` / `box_lower_sound` | `SatisfiesIntIneq x ⟨[(1, v)], 1⟩` / `⟨[(-1, v)], 0⟩` | `ProofStep::IntegerBoxBound` |

### `Monotone1in3Layer3/Certificate.lean`
| Lean 4 Theorem | Exact Signature | Rust `verifier.rs` Mapping |
|---|---|---|
| `checkStep_sound` | `SatisfiesFormula F x → StateSound x st → checkStep F st step = some st' → StateSound x st'` | Per-step loop in `verify_unsat_certificate` |
| `checkSteps_sound` | `SatisfiesFormula F x → StateSound x st → checkSteps F st cert = some st' → StateSound x st'` | Full trace loop in `verify_unsat_certificate` |
| `unified_certificate_sound` | `verifyCertificate F cert = true → ¬ ∃ x : Nat → Bool, SatisfiesFormula F x` | End-to-end soundness of `verify_unsat_certificate` |

### `Monotone1in3Layer3/Examples.lean`
| Theorem | Description |
|---|---|
| `parity_example_unsat` | Concrete $\mathbb{F}_2$ parity contradiction (`[(0,1,2), (0,1,3), (2,3,0), (0,0,4)]`) verified via `verifyCertificate` (`decide`) + `unified_certificate_sound`. |
| `k4_3_unsat` | Concrete $K_4^3$ refutation via divisor-3 Gomory–Chvátal cuts (`3*S ≤ 4 → S ≤ 1`, `-3*S ≤ -4 → -S ≤ -2`, `0 ≤ -1`). |
| `php2_3_unsat` | Concrete Pigeonhole Principle $\text{PHP}_2^3$ refutation via divisor-2 Gomory–Chvátal clique cuts (`2*S ≤ 3 → S ≤ 1` for both holes + 3 pigeon lower bounds $\implies$ `0 ≤ -1`). |

### `Monotone1in3Layer3/GeneratedCerts/VerifyBridge.lean` (End-to-End Rust $\to$ Lean 4 Kernel Certificates)
| Theorem | Exported Rust Instance | Scale ($n, m$) | Pruned Steps | Verification Mode |
|---|---|---:|---:|---|
| `tseitin_610_unsat` | `F3_tseitin_expander_unsat_t600_s20324691` (`Tseitin610Cert.lean`) | $610, 433$ | 626 (from 3,780) | Pure kernel (`by decide`) |
| `php_637_unsat` | `F5_pigeonhole_PHP9_10_s20332763` (`Pigeonhole637Cert.lean`) | $637, 556$ | 1,914 (from 9,936) | Pure kernel (`by decide`) |
| `hybrid_f2_z_783_unsat` | `F6_hybrid_f2_z_unsat_trap_t600_s20274242` (`HybridF2Z600Cert.lean`) | $783, 580$ | 1,329 (from 11,629) | Pure kernel (`by decide`) |

*(Note: `Certificate.lean` also includes machine-checked soundness proofs for `.integerEquivLift`, `.unitOneForcesZero`, and `.unitTwoZerosForceOne` used by `HybridF2Z600Cert.lean`.)*
