import Monotone1in3Layer3.Semantics

/-!
# Soundness of Gomory–Chvátal Integer Cutting Planes (Z-Dual)

Formalizes `IntLinearIneq`, non-negative linear combinations (`lin_comb_sound`),
coefficient merging/simplification (`simplify_ineq_sound`), exact-divisibility
Gomory–Chvátal floor rounding (`gomory_chvatal_cut_sound`), and `0 ≤ -1`
contradiction soundness (`integer_contradiction_sound`).
Zero `sorry` placeholders.
-/

namespace Monotone1in3

/-- A Z-linear inequality `∑ (c, v) ∈ coeffs, c * bitInt (x v) ≤ rhs`. -/
structure IntLinearIneq where
  coeffs : List (Int × Nat)
  rhs : Int
  deriving DecidableEq, Repr

/-- Evaluate the integer linear form `∑ c_i * bitInt (x v_i)`. -/
def evalLin (x : Nat → Bool) : List (Int × Nat) → Int
  | [] => 0
  | (c, v) :: rest => c * bitInt (x v) + evalLin x rest

/-- Satisfaction of an integer linear inequality under assignment `x`. -/
def SatisfiesIntIneq (x : Nat → Bool) (ineq : IntLinearIneq) : Prop :=
  evalLin x ineq.coeffs ≤ ineq.rhs

/-- Scale an inequality by integer `lam`. -/
def scaleIneq (lam : Int) (ineq : IntLinearIneq) : IntLinearIneq :=
  ⟨ineq.coeffs.map (fun (c, v) => (lam * c, v)), lam * ineq.rhs⟩

/-- Add two inequalities. -/
def addIneq (i1 i2 : IntLinearIneq) : IntLinearIneq :=
  ⟨i1.coeffs ++ i2.coeffs, i1.rhs + i2.rhs⟩

theorem evalLin_append (x : Nat → Bool) (l1 l2 : List (Int × Nat)) :
    evalLin x (l1 ++ l2) = evalLin x l1 + evalLin x l2 := by
  induction l1 with
  | nil => simp [evalLin]
  | cons cv rest ih =>
    rcases cv with ⟨c, v⟩
    simp [evalLin, ih, Int.add_assoc]

theorem evalLin_scale (x : Nat → Bool) (lam : Int) (l : List (Int × Nat)) :
    evalLin x (l.map (fun (c, v) => (lam * c, v))) = lam * evalLin x l := by
  induction l with
  | nil => simp [evalLin]
  | cons cv rest ih =>
    rcases cv with ⟨c, v⟩
    simp [evalLin, ih, Int.mul_add, Int.mul_assoc]

/-- Non-negative scaling preserves integer inequality satisfaction. -/
theorem scale_ineq_sound (x : Nat → Bool) (lam : Int) (ineq : IntLinearIneq)
    (hlam : 0 ≤ lam) (h : SatisfiesIntIneq x ineq) :
    SatisfiesIntIneq x (scaleIneq lam ineq) := by
  unfold SatisfiesIntIneq scaleIneq at *
  rw [evalLin_scale]
  exact Int.mul_le_mul_of_nonneg_left h hlam

/-- Addition of two satisfied inequalities preserves satisfaction. -/
theorem add_ineq_sound (x : Nat → Bool) (i1 i2 : IntLinearIneq)
    (h1 : SatisfiesIntIneq x i1) (h2 : SatisfiesIntIneq x i2) :
    SatisfiesIntIneq x (addIneq i1 i2) := by
  unfold SatisfiesIntIneq addIneq at *
  rw [evalLin_append]
  exact Int.add_le_add h1 h2

/-- Combine a list of `(multiplier, inequality)` pairs into a single linear combination. -/
def linComb : List (Int × IntLinearIneq) → IntLinearIneq
  | [] => ⟨[], 0⟩
  | (lam, ineq) :: rest => addIneq (scaleIneq lam ineq) (linComb rest)

/-- Any non-negative integer combination of satisfied inequalities is satisfied. -/
theorem lin_comb_sound (x : Nat → Bool) (terms : List (Int × IntLinearIneq))
    (h_nonneg : ∀ t ∈ terms, 0 ≤ t.1)
    (h_sat : ∀ t ∈ terms, SatisfiesIntIneq x t.2) :
    SatisfiesIntIneq x (linComb terms) := by
  induction terms with
  | nil =>
    simp [linComb, SatisfiesIntIneq, evalLin]
  | cons hd tl ih =>
    rcases hd with ⟨lam, ineq⟩
    simp only [linComb]
    apply add_ineq_sound
    · apply scale_ineq_sound x lam ineq
      · exact h_nonneg (lam, ineq) List.mem_cons_self
      · exact h_sat (lam, ineq) List.mem_cons_self
    · apply ih
      · intro t ht; exact h_nonneg t (List.mem_cons_of_mem _ ht)
      · intro t ht; exact h_sat t (List.mem_cons_of_mem _ ht)

/-- Merge a `(c, v)` term into an associative list of `(coeff, var)` pairs, dropping zeros. -/
def insertTerm (c : Int) (v : Nat) : List (Int × Nat) → List (Int × Nat)
  | [] => if c == 0 then [] else [(c, v)]
  | (c', v') :: rest =>
    if v == v' then
      let s := c + c'
      if s == 0 then rest else (s, v') :: rest
    else
      (c', v') :: insertTerm c v rest

theorem evalLin_insertTerm (x : Nat → Bool) (c : Int) (v : Nat) (l : List (Int × Nat)) :
    evalLin x (insertTerm c v l) = c * bitInt (x v) + evalLin x l := by
  induction l with
  | nil =>
    by_cases hc : c = 0
    · subst hc; simp [insertTerm, evalLin]
    · have hbeq : (c == 0) = false := beq_false_of_ne hc
      simp [insertTerm, hbeq, evalLin]
  | cons hd rest ih =>
    rcases hd with ⟨c', v'⟩
    by_cases hv : v = v'
    · subst hv
      by_cases hs : c + c' = 0
      · have hbeq : (c + c' == 0) = true := beq_iff_eq.mpr hs
        simp [insertTerm, hbeq, evalLin]
        cases x v <;> simp <;> omega
      · have hbeq : (c + c' == 0) = false := beq_false_of_ne hs
        simp [insertTerm, hbeq, evalLin]
        rw [Int.add_mul]
        omega
    · have hbeq : (v == v') = false := beq_false_of_ne hv
      simp [insertTerm, hbeq, evalLin, ih]
      omega

/-- Simplify coefficient list by merging duplicate variables and dropping 0-coeff terms. -/
def simplifyCoeffs (l : List (Int × Nat)) : List (Int × Nat) :=
  l.foldl (fun acc (c, v) => insertTerm c v acc) []

private theorem evalLin_foldl_insert (x : Nat → Bool) (acc l : List (Int × Nat)) :
    evalLin x (l.foldl (fun a (c, v) => insertTerm c v a) acc) = evalLin x acc + evalLin x l := by
  induction l generalizing acc with
  | nil => simp [evalLin]
  | cons hd rest ih =>
    rcases hd with ⟨c, v⟩
    simp only [List.foldl_cons, evalLin]
    rw [ih, evalLin_insertTerm]
    omega

theorem evalLin_simplifyCoeffs (x : Nat → Bool) (l : List (Int × Nat)) :
    evalLin x (simplifyCoeffs l) = evalLin x l := by
  unfold simplifyCoeffs
  rw [evalLin_foldl_insert]
  simp [evalLin]

theorem simplify_ineq_sound (x : Nat → Bool) (ineq : IntLinearIneq)
    (h : SatisfiesIntIneq x ineq) :
    SatisfiesIntIneq x ⟨simplifyCoeffs ineq.coeffs, ineq.rhs⟩ := by
  unfold SatisfiesIntIneq at *
  rw [evalLin_simplifyCoeffs]
  exact h

/-- Factor out a divisor `d` from `evalLin` when every coefficient is divisible by `d`. -/
theorem evalLin_div_factor (x : Nat → Bool) (d : Int) (l : List (Int × Nat))
    (hdiv : ∀ p ∈ l, p.1 % d = 0) :
    evalLin x l = d * evalLin x (l.map (fun (c, v) => (c / d, v))) := by
  induction l with
  | nil => simp [evalLin]
  | cons hd rest ih =>
    rcases hd with ⟨c, v⟩
    have hc : c % d = 0 := hdiv (c, v) List.mem_cons_self
    have hrest : ∀ p ∈ rest, p.1 % d = 0 := fun p hp => hdiv p (List.mem_cons_of_mem _ hp)
    have hmul : d * (c / d) = c := Int.mul_ediv_cancel' (Int.dvd_of_emod_eq_zero hc)
    simp only [List.map_cons, evalLin]
    rw [ih hrest, Int.mul_add, ← Int.mul_assoc, hmul]

/-- Exact integer floor-division lemma: if `d > 0` and `d * s ≤ b`, then `s ≤ b / d` (`Int.ediv`,
    which equals floor division `Int.fdiv` for positive `d > 0`). -/
theorem int_le_ediv_of_mul_le (d s b : Int) (hd : 0 < d) (h : d * s ≤ b) :
    s ≤ b / d := by
  rw [Int.le_ediv_iff_mul_le hd, Int.mul_comm]
  exact h

/-- **Soundness of Gomory–Chvátal Cutting Planes (`IntegerCut`)**:
    If `d > 0` divides every coefficient of `ineq`, then dividing every coefficient by `d`
    and taking exact integer floor division `rhs / d` preserves satisfaction. -/
theorem gomory_chvatal_cut_sound (x : Nat → Bool) (d : Int) (ineq : IntLinearIneq)
    (hd : 0 < d)
    (hdiv : ∀ p ∈ ineq.coeffs, p.1 % d = 0)
    (h : SatisfiesIntIneq x ineq) :
    SatisfiesIntIneq x ⟨ineq.coeffs.map (fun (c, v) => (c / d, v)), ineq.rhs / d⟩ := by
  unfold SatisfiesIntIneq at *
  rw [evalLin_div_factor x d ineq.coeffs hdiv] at h
  exact int_le_ediv_of_mul_le d _ ineq.rhs hd h

/-- **Soundness of Integer Contradiction (`0 ≤ -1`)**: empty LHS with `rhs < 0` implies `False`. -/
theorem integer_contradiction_sound (x : Nat → Bool) (rhs : Int)
    (h : SatisfiesIntIneq x ⟨[], rhs⟩) (hrhs : rhs < 0) :
    False := by
  simp only [SatisfiesIntIneq, evalLin] at h
  omega

/-- Clause upper lift soundness: `x_a + x_b + x_c ≤ 1`. -/
theorem clause_lift_upper_sound (x : Nat → Bool) (a b c : Nat) (h : Clause1in3 x a b c) :
    SatisfiesIntIneq x ⟨[(1, a), (1, b), (1, c)], 1⟩ := by
  simp only [SatisfiesIntIneq, evalLin]
  have hu := clause_z_upper x a b c h
  omega

/-- Clause lower lift soundness: `-x_a - x_b - x_c ≤ -1`. -/
theorem clause_lift_lower_sound (x : Nat → Bool) (a b c : Nat) (h : Clause1in3 x a b c) :
    SatisfiesIntIneq x ⟨[(-1, a), (-1, b), (-1, c)], -1⟩ := by
  simp only [SatisfiesIntIneq, evalLin]
  have hl := clause_z_lower x a b c h
  omega

/-- Box bound soundness: `x_v ≤ 1` and `-x_v ≤ 0`. -/
theorem box_upper_sound (x : Nat → Bool) (v : Nat) :
    SatisfiesIntIneq x ⟨[(1, v)], 1⟩ := by
  simp only [SatisfiesIntIneq, evalLin]
  have h := bitInt_le_one (x v)
  omega

theorem box_lower_sound (x : Nat → Bool) (v : Nat) :
    SatisfiesIntIneq x ⟨[(-1, v)], 0⟩ := by
  simp only [SatisfiesIntIneq, evalLin]
  have h := bitInt_nonneg (x v)
  omega

end Monotone1in3
