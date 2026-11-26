import Monotone1in3Layer3.Semantics
import Monotone1in3Layer3.F2AndGadgets
import Monotone1in3Layer3.CuttingPlanes

/-!
# End-to-End Unified Proof-Certificate Soundness (`verifyCertificate`)

Defines `UnifiedProofStep` mirroring `rust_layer2/src/verifier.rs` (including
`localClusterF2` and `integerConstLift`), uses a verified O(log N) persistent
binary trie (`PosMap`) so large Rust-exported proofs (n ≥ 610, ~2,000 steps)
reduce cleanly inside Lean 4's kernel, and proves:
  `unified_certificate_sound : verifyCertificate F cert = true → ¬ ∃ x, SatisfiesFormula F x`.
Zero `sorry` placeholders.
-/

namespace Monotone1in3

/-! ## Verified O(log N) Persistent Binary Trie (`PosMap`) -/

inductive PosMap (α : Type) where
  | leaf
  | node (val : Option α) (left right : PosMap α)

namespace PosMap

def get {α : Type} : PosMap α → Nat → Option α
  | .leaf, _ => none
  | .node vo l r, k =>
    if k == 0 then vo
    else if k % 2 == 0 then get l (k / 2)
    else get r (k / 2)

def setAux {α : Type} : Nat → PosMap α → Nat → α → PosMap α
  | 0, m, _, _ => m
  | fuel + 1, .leaf, k, v =>
    if k == 0 then .node (some v) .leaf .leaf
    else if k % 2 == 0 then .node none (setAux fuel .leaf (k / 2) v) .leaf
    else .node none .leaf (setAux fuel .leaf (k / 2) v)
  | fuel + 1, .node vo l r, k, v =>
    if k == 0 then .node (some v) l r
    else if k % 2 == 0 then .node vo (setAux fuel l (k / 2) v) r
    else .node vo l (setAux fuel r (k / 2) v)

def set {α : Type} (m : PosMap α) (k : Nat) (v : α) : PosMap α :=
  setAux 16 m k v

def All {α : Type} (P : α → Prop) : PosMap α → Prop
  | .leaf => True
  | .node vo l r => (∀ a, vo = some a → P a) ∧ All P l ∧ All P r

theorem All_get {α : Type} {P : α → Prop} {m : PosMap α} {k : Nat} {a : α}
    (hAll : All P m) (hGet : m.get k = some a) : P a := by
  induction m generalizing k with
  | leaf => simp [get] at hGet
  | node vo l r ihl ihr =>
    rcases hAll with ⟨hvo, hl, hr⟩
    unfold get at hGet
    by_cases hk : k = 0
    · subst hk
      simp at hGet
      exact hvo a hGet
    · have hk0 : (k == 0) = false := beq_false_of_ne hk
      simp only [hk0, Bool.false_eq_true, ↓reduceIte] at hGet
      by_cases hmod : k % 2 = 0
      · have hm : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
        simp only [hm, ↓reduceIte] at hGet
        exact ihl hl hGet
      · have hm : (k % 2 == 0) = false := beq_false_of_ne hmod
        simp only [hm, Bool.false_eq_true, ↓reduceIte] at hGet
        exact ihr hr hGet

theorem All_setAux {α : Type} {P : α → Prop} (fuel : Nat) {m : PosMap α} {k : Nat} {v : α}
    (hAll : All P m) (hv : P v) : All P (setAux fuel m k v) := by
  induction fuel generalizing m k with
  | zero => exact hAll
  | succ f ih =>
    cases m with
    | leaf =>
      simp only [setAux]
      by_cases hk : k = 0
      · subst hk; simp [All]; exact hv
      · have hk0 : (k == 0) = false := beq_false_of_ne hk
        simp only [hk0, Bool.false_eq_true, ↓reduceIte]
        by_cases hmod : k % 2 = 0
        · have hm : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
          simp only [hm, ↓reduceIte, All]
          refine ⟨?_, ih (m := PosMap.leaf) trivial, trivial⟩
          intro _ h; cases h
        · have hm : (k % 2 == 0) = false := beq_false_of_ne hmod
          simp only [hm, Bool.false_eq_true, ↓reduceIte, All]
          refine ⟨?_, trivial, ih (m := PosMap.leaf) trivial⟩
          intro _ h; cases h
    | node vo l r =>
      rcases hAll with ⟨hvo, hl, hr⟩
      simp only [setAux]
      by_cases hk : k = 0
      · subst hk; simp [All]; exact ⟨hv, hl, hr⟩
      · have hk0 : (k == 0) = false := beq_false_of_ne hk
        simp only [hk0, Bool.false_eq_true, ↓reduceIte]
        by_cases hmod : k % 2 = 0
        · have hm : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
          simp only [hm, ↓reduceIte, All]
          exact ⟨hvo, ih hl, hr⟩
        · have hm : (k % 2 == 0) = false := beq_false_of_ne hmod
          simp only [hm, Bool.false_eq_true, ↓reduceIte, All]
          exact ⟨hvo, hl, ih hr⟩

theorem All_set {α : Type} {P : α → Prop} {m : PosMap α} {k : Nat} {v : α}
    (hAll : All P m) (hv : P v) : All P (m.set k v) :=
  All_setAux 16 hAll hv

def fromListAux {α : Type} (idx : Nat) (acc : PosMap α) : List α → PosMap α
  | [] => acc
  | a :: rest => fromListAux (idx + 1) (acc.set idx a) rest

theorem All_fromListAux {α : Type} {P : α → Prop} (idx : Nat) (acc : PosMap α) (l : List α)
    (hAcc : All P acc) (hL : ∀ a ∈ l, P a) :
    All P (fromListAux idx acc l) := by
  induction l generalizing idx acc with
  | nil => exact hAcc
  | cons hd tl ih =>
    apply ih (idx + 1) (acc.set idx hd)
    · exact All_set hAcc (hL hd List.mem_cons_self)
    · intro a ha; exact hL a (List.mem_cons_of_mem _ ha)

def fromList {α : Type} (l : List α) : PosMap α :=
  fromListAux 0 .leaf l

theorem All_fromList {α : Type} {P : α → Prop} (l : List α) (hL : ∀ a ∈ l, P a) :
    All P (fromList l) :=
  All_fromListAux 0 .leaf l trivial hL

end PosMap

/-! ## Local Cluster Truth-Table Checker (Executable & Sound) -/

def setAssign (assign : Nat → Bool) (v : Nat) (b : Bool) : Nat → Bool :=
  fun u => if u == v then b else assign u

def clauseHoldsBool (assign : Nat → Bool) (a b c : Nat) : Bool :=
  bit (assign a) + bit (assign b) + bit (assign c) == 1

def allClausesHold (fMap : PosMap (Nat × Nat × Nat)) (assign : Nat → Bool) : List Nat → Bool
  | [] => true
  | cid :: rest =>
    match fMap.get cid with
    | none => false
    | some (a, b, c) => clauseHoldsBool assign a b c && allClausesHold fMap assign rest

def existsAuxSat (fMap : PosMap (Nat × Nat × Nat)) (cids : List Nat) :
    List Nat → (Nat → Bool) → Bool
  | [], assign => allClausesHold fMap assign cids
  | av :: rest, assign =>
    existsAuxSat fMap cids rest (setAssign assign av false) ||
    existsAuxSat fMap cids rest (setAssign assign av true)

def allSubclustersSat (fMap : PosMap (Nat × Nat × Nat)) (assign : Nat → Bool) :
    List (List Nat × List Nat) → Bool
  | [] => true
  | (cids, aux) :: rest =>
    existsAuxSat fMap cids aux assign && allSubclustersSat fMap assign rest

def checkCoreAll (fMap : PosMap (Nat × Nat × Nat))
    (subclusters : List (List Nat × List Nat))
    (eqVars : List Nat) (rhs : Bool) :
    List Nat → (Nat → Bool) → Bool
  | [], assign =>
    if allSubclustersSat fMap assign subclusters then
      evalF2 assign eqVars == rhs
    else
      true
  | cv :: rest, assign =>
    checkCoreAll fMap subclusters eqVars rhs rest (setAssign assign cv false) &&
    checkCoreAll fMap subclusters eqVars rhs rest (setAssign assign cv true)

def applyConstRefs : List (Nat × Bool × Nat) → (Nat → Bool) → (Nat → Bool)
  | [], assign => assign
  | (v, val, _) :: rest, assign => applyConstRefs rest (setAssign assign v val)

def checkConstRefs (f2Map : PosMap F2Constraint) : List (Nat × Bool × Nat) → Bool
  | [] => true
  | (v, val, lid) :: rest =>
    match f2Map.get lid with
    | some c => (c.vars == [v] && c.rhs == val) && checkConstRefs f2Map rest
    | none => false

def clauseVarsCovered (fMap : PosMap (Nat × Nat × Nat)) (allowed : List Nat) : List Nat → Bool
  | [] => true
  | cid :: rest =>
    match fMap.get cid with
    | none => false
    | some (a, b, c) =>
      allowed.contains a && allowed.contains b && allowed.contains c &&
      clauseVarsCovered fMap allowed rest

def subclustersCovered (fMap : PosMap (Nat × Nat × Nat)) (baseVars : List Nat) :
    List (List Nat × List Nat) → Bool
  | [] => true
  | (cids, aux) :: rest =>
    clauseVarsCovered fMap (aux ++ baseVars) cids && subclustersCovered fMap baseVars rest

def varsSubset (sub sup : List Nat) : Bool :=
  sub.all (fun v => sup.contains v)

/-! ## Soundness Lemmas for Local Cluster Truth-Table Checking -/

private theorem mem_of_contains_true {l : List Nat} {v : Nat} (h : l.contains v = true) : v ∈ l := by
  simpa [List.contains_eq_mem] using h

private theorem evalF2_eq_of_agrees (x assign : Nat → Bool) (vars : List Nat)
    (h : ∀ v ∈ vars, assign v = x v) :
    evalF2 assign vars = evalF2 x vars := by
  induction vars with
  | nil => rfl
  | cons v vs ih =>
    simp only [evalF2]
    rw [h v List.mem_cons_self, ih (fun u hu => h u (List.mem_cons_of_mem _ hu))]

private theorem clauseVarsCovered_mono (fMap : PosMap (Nat × Nat × Nat)) (l1 l2 : List Nat)
    (hsub : ∀ u, u ∈ l1 → u ∈ l2) (cids : List Nat)
    (h : clauseVarsCovered fMap l1 cids = true) :
    clauseVarsCovered fMap l2 cids = true := by
  induction cids with
  | nil => rfl
  | cons cid rest ih =>
    simp only [clauseVarsCovered] at h ⊢
    cases hg : fMap.get cid with
    | none => simp [hg] at h
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      simp [hg] at h ⊢
      rcases h with ⟨⟨⟨ha, hb⟩, hc⟩, hr⟩
      exact ⟨⟨⟨hsub a ha, hsub b hb⟩, hsub c hc⟩, ih hr⟩

private theorem allClausesHold_of_agrees (fMap : PosMap (Nat × Nat × Nat))
    (x assign : Nat → Bool)
    (hF : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) fMap)
    (allowed : List Nat) (cids : List Nat)
    (hCov : clauseVarsCovered fMap allowed cids = true)
    (hAg : ∀ v ∈ allowed, assign v = x v) :
    allClausesHold fMap assign cids = true := by
  induction cids with
  | nil => rfl
  | cons cid rest ih =>
    simp only [clauseVarsCovered, allClausesHold] at hCov ⊢
    cases hget : fMap.get cid with
    | none => simp [hget] at hCov
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      simp [hget] at hCov
      rcases hCov with ⟨⟨⟨ha, hb⟩, hc⟩, hrest⟩
      have hcl : Clause1in3 x a b c :=
        PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
      have hhold : clauseHoldsBool assign a b c = true := by
        unfold clauseHoldsBool
        rw [hAg a ha, hAg b hb, hAg c hc]
        exact beq_iff_eq.mpr hcl
      simp [hhold, ih hrest]

private theorem existsAuxSat_of_agrees (fMap : PosMap (Nat × Nat × Nat))
    (x assign : Nat → Bool)
    (hF : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) fMap)
    (baseVars aux : List Nat) (cids : List Nat)
    (hCov : clauseVarsCovered fMap (aux ++ baseVars) cids = true)
    (hAg : ∀ v ∈ baseVars, assign v = x v) :
    existsAuxSat fMap cids aux assign = true := by
  induction aux generalizing assign baseVars with
  | nil =>
    exact allClausesHold_of_agrees fMap x assign hF baseVars cids hCov hAg
  | cons av rest ih =>
    simp only [existsAuxSat, Bool.or_eq_true]
    have hCov' : clauseVarsCovered fMap (rest ++ (av :: baseVars)) cids = true := by
      apply clauseVarsCovered_mono fMap ((av :: rest) ++ baseVars) (rest ++ (av :: baseVars)) _ cids hCov
      intro u hu
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hu ⊢
      rcases hu with rfl | hr | hb
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hr
      · exact Or.inr (Or.inr hb)
    have hAgNext : ∀ v ∈ av :: baseVars, setAssign assign av (x av) v = x v := by
      intro v hv
      unfold setAssign
      by_cases hveq : v = av
      · subst hveq; simp
      · have hb : (v == av) = false := beq_false_of_ne hveq
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        cases hv with
        | head => exact absurd rfl hveq
        | tail _ hmem => exact hAg v hmem
    have hSat := ih (setAssign assign av (x av)) (av :: baseVars) hCov' hAgNext
    cases hx : x av
    · rw [hx] at hSat; exact Or.inl hSat
    · rw [hx] at hSat; exact Or.inr hSat

private theorem allSubclustersSat_of_agrees (fMap : PosMap (Nat × Nat × Nat))
    (x assign : Nat → Bool)
    (hF : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) fMap)
    (baseVars : List Nat) (subs : List (List Nat × List Nat))
    (hCov : subclustersCovered fMap baseVars subs = true)
    (hAg : ∀ v ∈ baseVars, assign v = x v) :
    allSubclustersSat fMap assign subs = true := by
  induction subs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨cids, aux⟩
    simp only [subclustersCovered, allSubclustersSat, Bool.and_eq_true] at hCov ⊢
    exact ⟨existsAuxSat_of_agrees fMap x assign hF baseVars aux cids hCov.1 hAg, ih hCov.2⟩

private theorem subclustersCovered_mono (fMap : PosMap (Nat × Nat × Nat)) (l1 l2 : List Nat)
    (hsub : ∀ u, u ∈ l1 → u ∈ l2) (subs : List (List Nat × List Nat))
    (h : subclustersCovered fMap l1 subs = true) :
    subclustersCovered fMap l2 subs = true := by
  induction subs with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨cids, aux⟩
    simp only [subclustersCovered, Bool.and_eq_true] at h ⊢
    refine ⟨clauseVarsCovered_mono fMap (aux ++ l1) (aux ++ l2) ?_ cids h.1, ih h.2⟩
    intro u hu
    simp only [List.mem_append] at hu ⊢
    rcases hu with ha | hl
    · exact Or.inl ha
    · exact Or.inr (hsub u hl)

private theorem checkCoreAll_sound (fMap : PosMap (Nat × Nat × Nat))
    (x : Nat → Bool)
    (hF : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) fMap)
    (subs : List (List Nat × List Nat))
    (eqVars : List Nat) (rhs : Bool)
    (constVars coreVars : List Nat) (assign : Nat → Bool)
    (hCheck : checkCoreAll fMap subs eqVars rhs coreVars assign = true)
    (hCov : subclustersCovered fMap (coreVars ++ constVars) subs = true)
    (hEqSub : varsSubset eqVars (coreVars ++ constVars) = true)
    (hAg : ∀ v ∈ constVars, assign v = x v) :
    evalF2 x eqVars = rhs := by
  induction coreVars generalizing constVars assign with
  | nil =>
    simp only [checkCoreAll] at hCheck
    have hSubSat := allSubclustersSat_of_agrees fMap x assign hF constVars subs hCov hAg
    rw [hSubSat] at hCheck
    simp only [↓reduceIte, beq_iff_eq] at hCheck
    have hEqAg : ∀ v ∈ eqVars, assign v = x v := by
      intro v hv
      have hmem := List.all_eq_true.mp hEqSub v hv
      exact hAg v (mem_of_contains_true hmem)
    rw [← evalF2_eq_of_agrees x assign eqVars hEqAg]
    exact hCheck
  | cons cv rest ih =>
    simp only [checkCoreAll, Bool.and_eq_true] at hCheck
    have hNext : checkCoreAll fMap subs eqVars rhs rest (setAssign assign cv (x cv)) = true := by
      cases x cv
      · exact hCheck.1
      · exact hCheck.2
    have hAgNext : ∀ v ∈ cv :: constVars, setAssign assign cv (x cv) v = x v := by
      intro v hv
      unfold setAssign
      by_cases hveq : v = cv
      · subst hveq; simp
      · have hb : (v == cv) = false := beq_false_of_ne hveq
        simp only [hb, Bool.false_eq_true, ↓reduceIte]
        cases hv with
        | head => exact absurd rfl hveq
        | tail _ hm => exact hAg v hm
    have hSubList : ∀ u, u ∈ (cv :: rest) ++ constVars → u ∈ rest ++ (cv :: constVars) := by
      intro u hu
      simp only [List.cons_append, List.mem_cons, List.mem_append] at hu ⊢
      rcases hu with rfl | hr | hc
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hr
      · exact Or.inr (Or.inr hc)
    have hCovNext : subclustersCovered fMap (rest ++ cv :: constVars) subs = true :=
      subclustersCovered_mono fMap ((cv :: rest) ++ constVars) (rest ++ cv :: constVars) hSubList subs hCov
    have hEqNext : varsSubset eqVars (rest ++ cv :: constVars) = true := by
      unfold varsSubset at hEqSub ⊢
      rw [List.all_eq_true] at hEqSub ⊢
      intro u hu
      have hm := mem_of_contains_true (hEqSub u hu)
      simp only [List.contains_eq_mem, decide_eq_true_eq]
      exact hSubList u hm
    exact ih (cv :: constVars) (setAssign assign cv (x cv)) hNext hCovNext hEqNext hAgNext

private theorem applyConstRefs_agrees (f2Map : PosMap F2Constraint) (x assign : Nat → Bool)
    (hF2 : PosMap.All (SatisfiesF2 x) f2Map)
    (refs : List (Nat × Bool × Nat))
    (hCheck : checkConstRefs f2Map refs = true)
    (prev : List Nat) (hPrev : ∀ v ∈ prev, assign v = x v) :
    ∀ v ∈ (refs.map (fun r => r.1)) ++ prev, applyConstRefs refs assign v = x v := by
  induction refs generalizing assign prev with
  | nil => exact hPrev
  | cons hd tl ih =>
    rcases hd with ⟨u, val, lid⟩
    simp only [checkConstRefs] at hCheck
    cases hget : f2Map.get lid with
    | none => simp [hget] at hCheck
    | some c =>
      simp [hget] at hCheck
      rcases hCheck with ⟨⟨hvars, hrhs⟩, hrest⟩
      have hsat : SatisfiesF2 x c := PosMap.All_get hF2 hget
      have hxu : x u = val := by
        unfold SatisfiesF2 at hsat
        rw [hvars, hrhs] at hsat
        simpa [evalF2] using hsat
      have hAgNext : ∀ v ∈ u :: prev, setAssign assign u val v = x v := by
        intro v hv
        unfold setAssign
        by_cases hvu : v = u
        · subst hvu; simp [hxu]
        · have hb : (v == u) = false := beq_false_of_ne hvu
          simp only [hb, Bool.false_eq_true, ↓reduceIte]
          cases hv with
          | head => exact absurd rfl hvu
          | tail _ hm => exact hPrev v hm
      have hRec := ih (setAssign assign u val) hrest (u :: prev) hAgNext
      intro v hv
      apply hRec v
      simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hv ⊢
      rcases hv with rfl | htl | hp
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl htl
      · exact Or.inr (Or.inr hp)

/-! ## Unified Proof Steps & Executable Verifier -/

/-- Unified proof steps mirroring `rust_layer2/src/verifier.rs`. -/
inductive UnifiedProofStep where
  | clauseF2Axiom (cIdx : Nat)
  | f2Xor (lhs rhs : Nat)
  | dupLiteralZero (cIdx v : Nat)
  | tripleLiteralContradiction (cIdx : Nat)
  | localClusterF2
      (subclusters : List (List Nat × List Nat))
      (coreVars : List Nat)
      (constRefs : List (Nat × Bool × Nat))
      (eqVars : List Nat)
      (rhs : Bool)
  | integerClauseLift (cIdx : Nat) (isUpper : Bool)
  | integerBoxBound (v : Nat) (isUpper : Bool)
  | integerConstLift (constId v : Nat) (val : Bool) (isUpper : Bool)
  | integerEquivLift (eqId u v : Nat) (uMinusV : Bool)
  | unitOneForcesZero (cIdx constId u target : Nat)
  | unitTwoZerosForceOne (cIdx z1Id z2Id target : Nat)
  | integerCut (parents : List (Nat × Int)) (divisor : Int)
  | f2Contradiction (lemmaId : Nat)
  | integerContradiction (rowId : Nat)
  deriving Repr

/-- Checker state using O(log N) `PosMap` stores for F_2 lemmas and Z-linear inequalities. -/
structure VerifierState where
  f2Map : PosMap F2Constraint := .leaf
  f2Count : Nat := 0
  intMap : PosMap IntLinearIneq := .leaf
  intCount : Nat := 0
  refuted : Bool := false

def VerifierState.pushF2 (st : VerifierState) (c : F2Constraint) : VerifierState :=
  { st with f2Map := st.f2Map.set st.f2Count c, f2Count := st.f2Count + 1 }

def VerifierState.pushInt (st : VerifierState) (r : IntLinearIneq) : VerifierState :=
  { st with intMap := st.intMap.set st.intCount r, intCount := st.intCount + 1 }

/-- Resolve parent `(rowId, multiplier)` references against `intMap`, verifying `mult ≥ 0`. -/
def resolveParents (intMap : PosMap IntLinearIneq) :
    List (Nat × Int) → Option (List (Int × IntLinearIneq))
  | [] => some []
  | (rid, mult) :: rest =>
    if mult < 0 then
      none
    else
      match intMap.get rid, resolveParents intMap rest with
      | some row, some tail => some ((mult, row) :: tail)
      | _, _ => none

theorem resolveParents_sound (x : Nat → Bool) (intMap : PosMap IntLinearIneq)
    (hRows : PosMap.All (SatisfiesIntIneq x) intMap)
    (parents : List (Nat × Int)) (resolved : List (Int × IntLinearIneq))
    (hRes : resolveParents intMap parents = some resolved) :
    (∀ t ∈ resolved, 0 ≤ t.1) ∧ (∀ t ∈ resolved, SatisfiesIntIneq x t.2) := by
  induction parents generalizing resolved with
  | nil =>
    simp [resolveParents] at hRes
    subst hRes
    constructor <;> (intro _ h; cases h)
  | cons hd tl ih =>
    rcases hd with ⟨rid, mult⟩
    simp only [resolveParents] at hRes
    split at hRes
    · cases hRes
    · rename_i hge
      cases hget : intMap.get rid with
      | none => simp [hget] at hRes
      | some row =>
        cases htail : resolveParents intMap tl with
        | none => simp [hget, htail] at hRes
        | some restRes =>
          simp [hget, htail] at hRes
          subst hRes
          have h_ih := ih restRes htail
          refine ⟨?_, ?_⟩
          · intro t ht
            cases ht with
            | head => omega
            | tail _ hmem => exact h_ih.1 t hmem
          · intro t ht
            cases ht with
            | head => exact PosMap.All_get hRows hget
            | tail _ hmem => exact h_ih.2 t hmem

/-- Check a single `UnifiedProofStep`, returning updated `VerifierState` or `none` on error. -/
def checkStep (fMap : PosMap (Nat × Nat × Nat)) (st : VerifierState) (step : UnifiedProofStep) :
    Option VerifierState :=
  match step with
  | .clauseF2Axiom cIdx =>
    match fMap.get cIdx with
    | none => none
    | some (a, b, c) =>
      some (st.pushF2 ⟨f2XorReduce [a, b] [c], true⟩)
  | .f2Xor lhs rhs =>
    match st.f2Map.get lhs, st.f2Map.get rhs with
    | some c1, some c2 =>
      some (st.pushF2 ⟨f2XorReduce c1.vars c2.vars, xor c1.rhs c2.rhs⟩)
    | _, _ => none
  | .dupLiteralZero cIdx v =>
    match fMap.get cIdx with
    | some (a, b, c) =>
      if (a == v && b == v) || (a == v && c == v) || (b == v && c == v) then
        some (st.pushF2 ⟨[v], false⟩)
      else none
    | none => none
  | .tripleLiteralContradiction cIdx =>
    match fMap.get cIdx with
    | some (a, b, c) =>
      if a == b && b == c then
        some { st.pushF2 ⟨[], true⟩ with refuted := true }
      else none
    | none => none
  | .localClusterF2 subclusters coreVars constRefs eqVars rhs =>
    let constVars := constRefs.map (fun r => r.1)
    let initAssign := applyConstRefs constRefs (fun _ => false)
    if checkConstRefs st.f2Map constRefs
        && subclustersCovered fMap (coreVars ++ constVars) subclusters
        && varsSubset eqVars (coreVars ++ constVars)
        && checkCoreAll fMap subclusters eqVars rhs coreVars initAssign then
      some (st.pushF2 ⟨eqVars, rhs⟩)
    else
      none
  | .integerClauseLift cIdx isUpper =>
    match fMap.get cIdx with
    | none => none
    | some (a, b, c) =>
      let row : IntLinearIneq :=
        if isUpper then ⟨[(1, a), (1, b), (1, c)], 1⟩
        else ⟨[(-1, a), (-1, b), (-1, c)], -1⟩
      some (st.pushInt row)
  | .integerBoxBound v isUpper =>
    let row : IntLinearIneq :=
      if isUpper then ⟨[(1, v)], 1⟩ else ⟨[(-1, v)], 0⟩
    some (st.pushInt row)
  | .integerConstLift constId v val isUpper =>
    match st.f2Map.get constId with
    | some c =>
      if c.vars == [v] && c.rhs == val then
        let row : IntLinearIneq :=
          if isUpper then ⟨[(1, v)], bitInt val⟩
          else ⟨[(-1, v)], -(bitInt val)⟩
        some (st.pushInt row)
      else none
    | none => none
  | .integerEquivLift eqId u v uMinusV =>
    match st.f2Map.get eqId with
    | some c =>
      if (c.vars == [u, v] || c.vars == [v, u]) && c.rhs == false then
        let row : IntLinearIneq :=
          if uMinusV then ⟨[(1, u), (-1, v)], 0⟩
          else ⟨[(1, v), (-1, u)], 0⟩
        some (st.pushInt row)
      else none
    | none => none
  | .unitOneForcesZero cIdx constId u target =>
    match fMap.get cIdx, st.f2Map.get constId with
    | some (a, b, c), some lc =>
      if lc.vars == [u] && lc.rhs == true && u != target &&
         (a == u || b == u || c == u) && (a == target || b == target || c == target) then
        some (st.pushF2 ⟨[target], false⟩)
      else none
    | _, _ => none
  | .unitTwoZerosForceOne cIdx z1Id z2Id target =>
    match fMap.get cIdx, st.f2Map.get z1Id, st.f2Map.get z2Id with
    | some (a, b, c), some l1, some l2 =>
      let ok :=
        (a == target && ((l1.vars == [b] && l2.vars == [c]) || (l1.vars == [c] && l2.vars == [b]))) ||
        (b == target && ((l1.vars == [a] && l2.vars == [c]) || (l1.vars == [c] && l2.vars == [a]))) ||
        (c == target && ((l1.vars == [a] && l2.vars == [b]) || (l1.vars == [b] && l2.vars == [a])))
      if ok && l1.rhs == false && l2.rhs == false then
        some (st.pushF2 ⟨[target], true⟩)
      else none
    | _, _, _ => none
  | .integerCut parents divisor =>
    if divisor ≤ 0 then
      none
    else
      match resolveParents st.intMap parents with
      | none => none
      | some terms =>
        let raw := linComb terms
        let simpCoeffs := simplifyCoeffs raw.coeffs
        if simpCoeffs.all (fun p => p.1 % divisor == 0) then
          let cutRow : IntLinearIneq :=
            ⟨simpCoeffs.map (fun (c, v) => (c / divisor, v)), raw.rhs / divisor⟩
          some (st.pushInt cutRow)
        else
          none
  | .f2Contradiction lemmaId =>
    match st.f2Map.get lemmaId with
    | some c =>
      if c.vars.isEmpty && c.rhs == true then
        some { st with refuted := true }
      else none
    | none => none
  | .integerContradiction rowId =>
    match st.intMap.get rowId with
    | some row =>
      if row.coeffs.isEmpty && row.rhs < 0 then
        some { st with refuted := true }
      else none
    | none => none

/-- Run the verifier over a sequence of proof steps. -/
def checkSteps (fMap : PosMap (Nat × Nat × Nat)) :
    VerifierState → List UnifiedProofStep → Option VerifierState
  | st, [] => some st
  | st, s :: rest =>
    match checkStep fMap st s with
    | none => none
    | some st' => checkSteps fMap st' rest

/-- Top-level executable certificate verifier mirroring `rust_layer2::verifier::verify_unsat_certificate`. -/
def verifyCertificate (F : Formula1in3) (cert : List UnifiedProofStep) : Bool :=
  match checkSteps (PosMap.fromList F) {} cert with
  | some st => st.refuted
  | none => false

/-- Semantic invariant preserved across every step of `checkStep`. -/
def StateSound (x : Nat → Bool) (st : VerifierState) : Prop :=
  PosMap.All (SatisfiesF2 x) st.f2Map ∧
  PosMap.All (SatisfiesIntIneq x) st.intMap ∧
  (st.refuted = true → False)

theorem checkStep_sound (fMap : PosMap (Nat × Nat × Nat)) (x : Nat → Bool)
    (hF : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) fMap)
    (st st' : VerifierState) (step : UnifiedProofStep)
    (hInv : StateSound x st)
    (hStep : checkStep fMap st step = some st') :
    StateSound x st' := by
  rcases hInv with ⟨hF2, hInt, hRef⟩
  cases step with
  | clauseF2Axiom cIdx =>
    simp only [checkStep] at hStep
    cases hget : fMap.get cIdx with
    | none => simp [hget] at hStep
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      simp [hget] at hStep
      subst hStep
      refine ⟨PosMap.All_set hF2 ?_, hInt, hRef⟩
      have hcl : Clause1in3 x a b c := PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
      exact clause_to_f2_sound x a b c hcl
  | f2Xor lhs rhs =>
    simp only [checkStep] at hStep
    cases h1 : st.f2Map.get lhs with
    | none => simp [h1] at hStep
    | some c1 =>
      cases h2 : st.f2Map.get rhs with
      | none => simp [h1, h2] at hStep
      | some c2 =>
        simp [h1, h2] at hStep
        subst hStep
        refine ⟨PosMap.All_set hF2 ?_, hInt, hRef⟩
        exact f2_xor_reduce_sound x c1 c2 (PosMap.All_get hF2 h1) (PosMap.All_get hF2 h2)
  | dupLiteralZero cIdx v =>
    simp only [checkStep] at hStep
    cases hget : fMap.get cIdx with
    | none => simp [hget] at hStep
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      simp [hget] at hStep
      rcases hStep with ⟨hdup, rfl⟩
      refine ⟨PosMap.All_set hF2 ?_, hInt, hRef⟩
      have hcl : Clause1in3 x a b c := PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
      unfold SatisfiesF2 evalF2
      unfold Clause1in3 at hcl
      rcases hdup with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
      · cases hb : x b <;> cases hc : x c <;> simp [evalF2, hb, hc] at hcl ⊢
      · cases hc : x c <;> cases hb : x b <;> simp [evalF2, hc, hb] at hcl ⊢
      · cases hc : x c <;> cases ha : x a <;> simp [evalF2, hc, ha] at hcl ⊢
  | tripleLiteralContradiction cIdx =>
    simp only [checkStep] at hStep
    cases hget : fMap.get cIdx with
    | none => simp [hget] at hStep
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      simp [hget] at hStep
      rcases hStep with ⟨⟨rfl, rfl⟩, _⟩
      have hcl : Clause1in3 x a a a := PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
      exact False.elim (clause_triple_literal_false x a hcl)
  | localClusterF2 subclusters coreVars constRefs eqVars rhs =>
    simp only [checkStep] at hStep
    split at hStep
    · rename_i hcond
      simp only [Option.some.injEq] at hStep
      subst hStep
      simp only [Bool.and_eq_true] at hcond
      rcases hcond with ⟨⟨⟨hRefs, hCov⟩, hEqSub⟩, hCore⟩
      refine ⟨PosMap.All_set hF2 ?_, hInt, hRef⟩
      have hAg : ∀ v ∈ constRefs.map (fun r => r.1),
          applyConstRefs constRefs (fun _ => false) v = x v := by
        have h := applyConstRefs_agrees st.f2Map x (fun _ => false) hF2 constRefs hRefs []
          (fun _ hm => nomatch hm)
        simpa using h
      exact checkCoreAll_sound fMap x hF subclusters eqVars rhs
        (constRefs.map (fun r => r.1)) coreVars
        (applyConstRefs constRefs (fun _ => false))
        hCore hCov hEqSub hAg
    · cases hStep
  | integerClauseLift cIdx isUpper =>
    simp only [checkStep] at hStep
    cases hget : fMap.get cIdx with
    | none => simp [hget] at hStep
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      simp [hget] at hStep
      subst hStep
      refine ⟨hF2, PosMap.All_set hInt ?_, hRef⟩
      have hcl : Clause1in3 x a b c := PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
      cases isUpper
      · exact clause_lift_lower_sound x a b c hcl
      · exact clause_lift_upper_sound x a b c hcl
  | integerBoxBound v isUpper =>
    simp only [checkStep] at hStep
    simp at hStep
    subst hStep
    refine ⟨hF2, PosMap.All_set hInt ?_, hRef⟩
    cases isUpper
    · exact box_lower_sound x v
    · exact box_upper_sound x v
  | integerConstLift constId v val isUpper =>
    simp only [checkStep] at hStep
    cases hget : st.f2Map.get constId with
    | none => simp [hget] at hStep
    | some c =>
      simp [hget] at hStep
      rcases hStep with ⟨⟨hvars, hrhs⟩, rfl⟩
      have hsat : SatisfiesF2 x c := PosMap.All_get hF2 hget
      have hxv : x v = val := by
        unfold SatisfiesF2 at hsat
        rw [hvars, hrhs] at hsat
        simpa [evalF2] using hsat
      refine ⟨hF2, PosMap.All_set hInt ?_, hRef⟩
      cases isUpper
      · simp [SatisfiesIntIneq, evalLin, hxv]
      · simp [SatisfiesIntIneq, evalLin, hxv]
  | integerEquivLift eqId u v uMinusV =>
    simp only [checkStep] at hStep
    cases hget : st.f2Map.get eqId with
    | none => simp [hget] at hStep
    | some c =>
      simp [hget] at hStep
      rcases hStep with ⟨⟨hvars, hrhs⟩, rfl⟩
      have hsat : SatisfiesF2 x c := PosMap.All_get hF2 hget
      have hxeq : x u = x v := by
        unfold SatisfiesF2 at hsat
        rcases hvars with h1 | h2
        · rw [h1, hrhs] at hsat
          cases hxu : x u <;> cases hxv : x v <;> simp [evalF2, hxu, hxv] at hsat ⊢
        · rw [h2, hrhs] at hsat
          cases hxu : x u <;> cases hxv : x v <;> simp [evalF2, hxu, hxv] at hsat ⊢
      refine ⟨hF2, PosMap.All_set hInt ?_, hRef⟩
      cases uMinusV
      · simp [SatisfiesIntIneq, evalLin, hxeq]; omega
      · simp [SatisfiesIntIneq, evalLin, hxeq]; omega
  | unitOneForcesZero cIdx constId u target =>
    simp only [checkStep] at hStep
    cases hget : fMap.get cIdx with
    | none => simp [hget] at hStep
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      cases hl : st.f2Map.get constId with
      | none => simp [hget, hl] at hStep
      | some lc =>
        simp [hget, hl] at hStep
        rcases hStep with ⟨⟨⟨⟨⟨hvars, hrhs⟩, hne⟩, huin⟩, htin⟩, rfl⟩
        have hcl : Clause1in3 x a b c :=
          PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
        have hsat : SatisfiesF2 x lc := PosMap.All_get hF2 hl
        have hxu : x u = true := by
          unfold SatisfiesF2 at hsat
          rw [hvars, hrhs] at hsat
          simpa [evalF2] using hsat
        refine ⟨PosMap.All_set hF2 ?_, hInt, hRef⟩
        have hxt : x target = false := by
          unfold Clause1in3 bit at hcl
          cases ha : x a <;> cases hb : x b <;> cases hc : x c <;>
            rcases huin with (rfl | rfl) | rfl <;> rcases htin with (rfl | rfl) | rfl <;>
            simp_all
        simp [SatisfiesF2, evalF2, hxt]
  | unitTwoZerosForceOne cIdx z1Id z2Id target =>
    simp only [checkStep] at hStep
    cases hget : fMap.get cIdx with
    | none => simp [hget] at hStep
    | some cl =>
      rcases cl with ⟨a, b, c⟩
      cases hl1 : st.f2Map.get z1Id with
      | none => simp [hget, hl1] at hStep
      | some l1 =>
        cases hl2 : st.f2Map.get z2Id with
        | none => simp [hget, hl1, hl2] at hStep
        | some l2 =>
          simp [hget, hl1, hl2] at hStep
          rcases hStep with ⟨⟨⟨hok, hr1⟩, hr2⟩, rfl⟩
          have hcl : Clause1in3 x a b c :=
            PosMap.All_get (P := fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) hF hget
          have hs1 : SatisfiesF2 x l1 := PosMap.All_get hF2 hl1
          have hs2 : SatisfiesF2 x l2 := PosMap.All_get hF2 hl2
          refine ⟨PosMap.All_set hF2 ?_, hInt, hRef⟩
          have hxt : x target = true := by
            unfold Clause1in3 bit at hcl
            unfold SatisfiesF2 at hs1 hs2
            rcases hok with (⟨rfl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ | ⟨rfl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩) | ⟨rfl, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩ <;>
              (rw [h1, hr1] at hs1; rw [h2, hr2] at hs2; simp [evalF2] at hs1 hs2;
               cases ha : x a <;> cases hb : x b <;> cases hc : x c <;> simp_all)
          simp [SatisfiesF2, evalF2, hxt]
  | integerCut parents divisor =>
    simp only [checkStep] at hStep
    split at hStep
    · cases hStep
    · rename_i hpos
      have hd : 0 < divisor := by omega
      cases hres : resolveParents st.intMap parents with
      | none => simp [hres] at hStep
      | some terms =>
        simp [hres] at hStep
        rcases hStep with ⟨hall, rfl⟩
        refine ⟨hF2, PosMap.All_set hInt ?_, hRef⟩
        have ⟨hnn, hsat⟩ := resolveParents_sound x st.intMap hInt parents terms hres
        have hcomb := lin_comb_sound x terms hnn hsat
        have hsimp := simplify_ineq_sound x (linComb terms) hcomb
        have hdiv : ∀ p ∈ simplifyCoeffs (linComb terms).coeffs, p.1 % divisor = 0 := by
          intro p hp
          rcases p with ⟨c, v⟩
          exact hall c v hp
        exact gomory_chvatal_cut_sound x divisor
          ⟨simplifyCoeffs (linComb terms).coeffs, (linComb terms).rhs⟩ hd hdiv hsimp
  | f2Contradiction lemmaId =>
    simp only [checkStep] at hStep
    cases hget : st.f2Map.get lemmaId with
    | none => simp [hget] at hStep
    | some c =>
      simp [hget] at hStep
      rcases hStep with ⟨⟨hvars, hrhs⟩, _⟩
      have hc := PosMap.All_get hF2 hget
      rcases c with ⟨vars, rhs⟩
      simp at hvars hrhs
      subst hvars; subst hrhs
      exact False.elim (f2_contradiction_sound x hc)
  | integerContradiction rowId =>
    simp only [checkStep] at hStep
    cases hget : st.intMap.get rowId with
    | none => simp [hget] at hStep
    | some row =>
      simp [hget] at hStep
      rcases hStep with ⟨⟨hcoeffs, hrhs⟩, _⟩
      have hr := PosMap.All_get hInt hget
      rcases row with ⟨coeffs, rhs⟩
      simp at hcoeffs hrhs
      subst hcoeffs
      exact False.elim (integer_contradiction_sound x rhs hr hrhs)

theorem checkSteps_sound (fMap : PosMap (Nat × Nat × Nat)) (x : Nat → Bool)
    (hF : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) fMap)
    (cert : List UnifiedProofStep) (st st' : VerifierState)
    (hInv : StateSound x st)
    (hRun : checkSteps fMap st cert = some st') :
    StateSound x st' := by
  induction cert generalizing st with
  | nil =>
    simp [checkSteps] at hRun
    subst hRun
    exact hInv
  | cons s rest ih =>
    simp only [checkSteps] at hRun
    cases hs : checkStep fMap st s with
    | none => simp [hs] at hRun
    | some st1 =>
      simp [hs] at hRun
      exact ih st1 (checkStep_sound fMap x hF st st1 s hInv hs) hRun

/-- **End-to-End Unified Certificate Soundness Theorem**:
    If `verifyCertificate F cert = true`, then `F` has NO satisfying Monotone 1-in-3 assignment. -/
theorem unified_certificate_sound (F : Formula1in3) (cert : List UnifiedProofStep)
    (hCert : verifyCertificate F cert = true) :
    ¬ ∃ x : Nat → Bool, SatisfiesFormula F x := by
  rintro ⟨x, hF⟩
  unfold verifyCertificate at hCert
  cases hrun : checkSteps (PosMap.fromList F) {} cert with
  | none => simp [hrun] at hCert
  | some st =>
    simp [hrun] at hCert
    have hFMap : PosMap.All (fun cl => Clause1in3 x cl.1 cl.2.1 cl.2.2) (PosMap.fromList F) :=
      PosMap.All_fromList F hF
    have hInit : StateSound x {} := ⟨trivial, trivial, fun h => by cases h⟩
    have hFinal := checkSteps_sound (PosMap.fromList F) x hFMap cert {} st hInit hrun
    exact hFinal.2.2 hCert

end Monotone1in3
