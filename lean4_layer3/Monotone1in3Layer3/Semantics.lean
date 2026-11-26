/-!
# Exact Monotone 1-in-3 SAT Semantics & Core Soundness Bridges

Formalizes `Clause1in3`, `SatisfiesFormula`, the F_2 parity/annihilator bridge,
the Z-linear inequality bridge, and deterministic 1-in-3 unit-collapse cascades.
Zero `sorry` placeholders.
-/

namespace Monotone1in3

/-- Boolean-to-Nat bit encoding `{false ↦ 0, true ↦ 1}`. -/
@[simp] def bit (b : Bool) : Nat :=
  if b then 1 else 0

/-- Boolean-to-Int bit encoding `{false ↦ 0, true ↦ 1}`. -/
@[simp] def bitInt (b : Bool) : Int :=
  if b then 1 else 0

theorem bitInt_eq_ofNat_bit (b : Bool) : bitInt b = Int.ofNat (bit b) := by
  cases b <;> rfl

theorem bitInt_nonneg (b : Bool) : 0 ≤ bitInt b := by
  cases b <;> decide

theorem bitInt_le_one (b : Bool) : bitInt b ≤ 1 := by
  cases b <;> decide

/-- Exact Monotone 1-in-3 SAT clause semantics: `x_a + x_b + x_c = 1`. -/
def Clause1in3 (x : Nat → Bool) (a b c : Nat) : Prop :=
  bit (x a) + bit (x b) + bit (x c) = 1

/-- A Monotone 1-in-3 SAT formula is a list of variable-index triples `(a, b, c)`. -/
abbrev Formula1in3 := List (Nat × Nat × Nat)

/-- Global satisfaction of a Monotone 1-in-3 SAT formula under assignment `x`. -/
def SatisfiesFormula (F : Formula1in3) (x : Nat → Bool) : Prop :=
  ∀ cl ∈ F, Clause1in3 x cl.1 cl.2.1 cl.2.2

/-! ## 1. F_2 Parity & Quadratic Annihilator Bridges -/

/-- Every satisfied 1-in-3 clause satisfies `x_a + x_b + x_c ≡ 1 (mod 2)`. -/
theorem clause_f2_parity (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    (bit (x a) + bit (x b) + bit (x c)) % 2 = 1 := by
  unfold Clause1in3 at h
  omega

/-- Every satisfied 1-in-3 clause satisfies Boolean XOR parity `x_a ⊕ x_b ⊕ x_c = true`. -/
theorem clause_f2_xor (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    xor (xor (x a) (x b)) (x c) = true := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- Pairwise quadratic annihilator `x_a * x_b = 0`. -/
theorem clause_annihilator_ab (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    bit (x a) * bit (x b) = 0 := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- Pairwise quadratic annihilator `x_b * x_c = 0`. -/
theorem clause_annihilator_bc (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    bit (x b) * bit (x c) = 0 := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- Pairwise quadratic annihilator `x_a * x_c = 0`. -/
theorem clause_annihilator_ac (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    bit (x a) * bit (x c) = 0 := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- Duplicate literal rule: `(a, a, b)` forces `x_a = false`. -/
theorem clause_dup_literal_zero (x : Nat → Bool) (a b : Nat)
    (h : Clause1in3 x a a b) :
    x a = false := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> simp [ha, hb] at h ⊢

/-- Triple literal contradiction: `(a, a, a)` is unsatisfiable. -/
theorem clause_triple_literal_false (x : Nat → Bool) (a : Nat)
    (h : Clause1in3 x a a a) :
    False := by
  unfold Clause1in3 at h
  cases ha : x a <;> simp [ha] at h

/-! ## 2. Z-Linear Inequality Bridges -/

/-- Upper Z-linear inequality bridge: `x_a + x_b + x_c ≤ 1`. -/
theorem clause_z_upper (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    bitInt (x a) + bitInt (x b) + bitInt (x c) ≤ 1 := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- Lower Z-linear inequality bridge: `-x_a - x_b - x_c ≤ -1`. -/
theorem clause_z_lower (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) :
    -(bitInt (x a)) - bitInt (x b) - bitInt (x c) ≤ -1 := by
  unfold Clause1in3 at h
  cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-! ## 3. Soundness of Deterministic 1-in-3 Unit-Collapse Cascades -/

/-- Unit-collapse (true literal): `x_a = true` forces `x_b = false ∧ x_c = false`. -/
theorem unit_collapse_true (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) (ha : x a = true) :
    x b = false ∧ x c = false := by
  unfold Clause1in3 at h
  cases hb : x b <;> cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- Unit-collapse (two false literals): `x_a = false ∧ x_b = false` forces `x_c = true`. -/
theorem unit_collapse_two_false (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) (ha : x a = false) (hb : x b = false) :
    x c = true := by
  unfold Clause1in3 at h
  cases hc : x c <;> simp [ha, hb, hc] at h ⊢

/-- All-false clause contradiction. -/
theorem unit_all_false_contradiction (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) (ha : x a = false) (hb : x b = false) (hc : x c = false) :
    False := by
  unfold Clause1in3 at h
  simp [ha, hb, hc] at h

/-- Two-true clause contradiction. -/
theorem unit_two_true_contradiction (x : Nat → Bool) (a b c : Nat)
    (h : Clause1in3 x a b c) (ha : x a = true) (hb : x b = true) :
    False := by
  unfold Clause1in3 at h
  cases hc : x c <;> simp [ha, hb, hc] at h

end Monotone1in3
