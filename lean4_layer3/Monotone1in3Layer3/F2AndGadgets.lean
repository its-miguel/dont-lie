import Monotone1in3Layer3.Semantics

/-!
# Soundness of F_2 Parity & Local Gadget Projection Rules

Formalizes `F2Constraint`, XOR-combination with cancellation (`f2XorReduce`),
empty-LHS parity contradiction (`0 = 1 mod 2`), and `LocalClusterF2Axiom` soundness.
Zero `sorry` placeholders.
-/

namespace Monotone1in3

/-- An F_2 affine equation `⨁_{v ∈ vars} x_v = rhs`. -/
structure F2Constraint where
  vars : List Nat
  rhs : Bool
  deriving DecidableEq, Repr

/-- Evaluate the XOR parity of a list of variable indices under assignment `x`. -/
def evalF2 (x : Nat → Bool) : List Nat → Bool
  | [] => false
  | v :: vs => xor (x v) (evalF2 x vs)

/-- Satisfaction of an F_2 linear constraint under assignment `x`. -/
def SatisfiesF2 (x : Nat → Bool) (c : F2Constraint) : Prop :=
  evalF2 x c.vars = c.rhs

theorem evalF2_append (x : Nat → Bool) (l1 l2 : List Nat) :
    evalF2 x (l1 ++ l2) = xor (evalF2 x l1) (evalF2 x l2) := by
  induction l1 with
  | nil => simp [evalF2]
  | cons v vs ih =>
    simp [evalF2, ih]

/-- Toggle membership of variable `v` in a variable list (mod-2 cancellation). -/
def toggleVar (v : Nat) : List Nat → List Nat
  | [] => [v]
  | u :: us => if u == v then us else u :: toggleVar v us

theorem evalF2_toggleVar (x : Nat → Bool) (v : Nat) (l : List Nat) :
    evalF2 x (toggleVar v l) = xor (x v) (evalF2 x l) := by
  induction l with
  | nil => simp [toggleVar, evalF2]
  | cons u us ih =>
    by_cases huv : u = v
    · subst huv
      simp [toggleVar, evalF2]
    · have hbeq : (u == v) = false := beq_false_of_ne huv
      simp [toggleVar, hbeq, evalF2, ih]
      rw [← Bool.xor_assoc, ← Bool.xor_assoc, Bool.xor_comm (x u) (x v)]

/-- Exact XOR-reduction of two variable lists (cancels matching pairs mod 2). -/
def f2XorReduce (l1 l2 : List Nat) : List Nat :=
  l2.foldl (fun acc v => toggleVar v acc) l1

private theorem evalF2_foldl_toggle (x : Nat → Bool) (acc l : List Nat) :
    evalF2 x (l.foldl (fun a v => toggleVar v a) acc) = xor (evalF2 x acc) (evalF2 x l) := by
  induction l generalizing acc with
  | nil => simp [evalF2]
  | cons v vs ih =>
    simp only [List.foldl_cons, evalF2]
    rw [ih, evalF2_toggleVar]
    rw [Bool.xor_comm (x v) (evalF2 x acc), Bool.xor_assoc]

theorem evalF2_f2XorReduce (x : Nat → Bool) (l1 l2 : List Nat) :
    evalF2 x (f2XorReduce l1 l2) = xor (evalF2 x l1) (evalF2 x l2) :=
  evalF2_foldl_toggle x l1 l2

/-- XOR-combining two satisfied F_2 constraints (without reduction) preserves satisfaction. -/
theorem f2_xor_combine_sound (x : Nat → Bool) (c1 c2 : F2Constraint)
    (h1 : SatisfiesF2 x c1) (h2 : SatisfiesF2 x c2) :
    SatisfiesF2 x ⟨c1.vars ++ c2.vars, xor c1.rhs c2.rhs⟩ := by
  unfold SatisfiesF2 at *
  rw [evalF2_append, h1, h2]

/-- XOR-combining two satisfied F_2 constraints with mod-2 cancellation preserves satisfaction. -/
theorem f2_xor_reduce_sound (x : Nat → Bool) (c1 c2 : F2Constraint)
    (h1 : SatisfiesF2 x c1) (h2 : SatisfiesF2 x c2) :
    SatisfiesF2 x ⟨f2XorReduce c1.vars c2.vars, xor c1.rhs c2.rhs⟩ := by
  unfold SatisfiesF2 at *
  rw [evalF2_f2XorReduce, h1, h2]

/-- Empty-LHS parity contradiction: `0 = 1 (mod 2)` implies `False`. -/
theorem f2_contradiction_sound (x : Nat → Bool) (h : SatisfiesF2 x ⟨[], true⟩) : False := by
  unfold SatisfiesF2 evalF2 at h
  cases h

/-- Raw 1-in-3 clause `(a, b, c)` entails the F_2 axiom `x_a ⊕ x_b ⊕ x_c = true`. -/
theorem clause_to_f2_sound (x : Nat → Bool) (a b c : Nat) (h : Clause1in3 x a b c) :
    SatisfiesF2 x ⟨f2XorReduce [a, b] [c], true⟩ := by
  unfold SatisfiesF2
  rw [evalF2_f2XorReduce]
  have hx := clause_f2_xor x a b c h
  simp [evalF2] at hx ⊢
  simpa [Bool.xor_assoc] using hx

/-- A `LocalClusterF2Axiom` asserts that a local sub-formula `subF` (subset of global `F`)
    semantically entails an F_2 affine constraint `eq` over every truth assignment. -/
structure LocalClusterF2Axiom (F : Formula1in3) where
  subF : Formula1in3
  sub_subset : ∀ cl ∈ subF, cl ∈ F
  eq : F2Constraint
  entails : ∀ y : Nat → Bool, SatisfiesFormula subF y → SatisfiesF2 y eq

/-- Soundness of `LocalClusterF2Axiom`: any global satisfying assignment satisfies `ax.eq`. -/
theorem local_cluster_f2_sound (F : Formula1in3) (ax : LocalClusterF2Axiom F)
    (x : Nat → Bool) (hF : SatisfiesFormula F x) :
    SatisfiesF2 x ax.eq := by
  apply ax.entails x
  intro cl hcl
  exact hF cl (ax.sub_subset cl hcl)

end Monotone1in3
