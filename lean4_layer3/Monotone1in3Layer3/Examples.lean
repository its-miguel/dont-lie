import Monotone1in3Layer3.Certificate

/-!
# Machine-Checked Concrete Refutation Examples (Zero `sorry`)

1. **Odd-Parity Contradiction (`parity_example_unsat`):** Verified via `clauseF2Axiom`,
   `dupLiteralZero`, `f2Xor`, and `f2Contradiction`.
2. **K_4^3 Integer Cutting-Plane Refutation (`k4_3_unsat`):** Verified via `integerClauseLift`
   and divisor-3 Gomory–Chvátal cuts (`3*S ≤ 4 → S ≤ 1`, `-3*S ≤ -4 → -S ≤ -2`, `0 ≤ -1`).
3. **Pigeonhole Principle PHP_2^3 (`php2_3_unsat`):** Verified via divisor-2 Gomory–Chvátal
   clique cuts (`2*(p_{0,j} + p_{1,j} + p_{2,j}) ≤ 3 → p_{0,j} + p_{1,j} + p_{2,j} ≤ 1`)
   combined with 3 pigeon lower bounds (`0 ≤ 2 - 3 = -1`).
-/

namespace Monotone1in3.Examples

open Monotone1in3

/-! ## Example 1: F_2 Parity Contradiction -/

/-- Formula: (x0,x1,x2), (x0,x1,x3), (x2,x3,x0), (x0,x0,x4).
    XORing all 3 parity clauses + `x0 = 0` yields `0 = 1 (mod 2)`. -/
def parityFormula : Formula1in3 :=
  [(0, 1, 2), (0, 1, 3), (2, 3, 0), (0, 0, 4)]

def parityCert : List UnifiedProofStep :=
  [ .clauseF2Axiom 0            -- lemma 0: x0 ⊕ x1 ⊕ x2 = 1
  , .clauseF2Axiom 1            -- lemma 1: x0 ⊕ x1 ⊕ x3 = 1
  , .clauseF2Axiom 2            -- lemma 2: x2 ⊕ x3 ⊕ x0 = 1
  , .dupLiteralZero 3 0         -- lemma 3: x0 = 0
  , .f2Xor 0 1                  -- lemma 4: x2 ⊕ x3 = 0
  , .f2Xor 4 2                  -- lemma 5: x0 = 1
  , .f2Xor 5 3                  -- lemma 6: [] = 1 (0 = 1 mod 2)
  , .f2Contradiction 6
  ]

theorem parity_cert_checks : verifyCertificate parityFormula parityCert = true := by
  decide

theorem parity_example_unsat : ¬ ∃ x : Nat → Bool, SatisfiesFormula parityFormula x :=
  unified_certificate_sound parityFormula parityCert parity_cert_checks

/-! ## Example 2: K_4^3 via Divisor-3 Gomory–Chvátal Cutting Planes -/

def k4_3Formula : Formula1in3 :=
  [(0, 1, 2), (0, 1, 3), (0, 2, 3), (1, 2, 3)]

def k4_3Cert : List UnifiedProofStep :=
  [ .integerClauseLift 0 true   -- row 0: x0 + x1 + x2 ≤ 1
  , .integerClauseLift 1 true   -- row 1: x0 + x1 + x3 ≤ 1
  , .integerClauseLift 2 true   -- row 2: x0 + x2 + x3 ≤ 1
  , .integerClauseLift 3 true   -- row 3: x1 + x2 + x3 ≤ 1
  , .integerClauseLift 0 false  -- row 4: -x0 - x1 - x2 ≤ -1
  , .integerClauseLift 1 false  -- row 5: -x0 - x1 - x3 ≤ -1
  , .integerClauseLift 2 false  -- row 6: -x0 - x2 - x3 ≤ -1
  , .integerClauseLift 3 false  -- row 7: -x1 - x2 - x3 ≤ -1
  -- row 8: 3*(x0+x1+x2+x3) ≤ 4  ==> (div 3, floor) x0+x1+x2+x3 ≤ 1
  , .integerCut [(0, 1), (1, 1), (2, 1), (3, 1)] 3
  -- row 9: -3*(x0+x1+x2+x3) ≤ -4 ==> (div 3, floor) -x0-x1-x2-x3 ≤ -2
  , .integerCut [(4, 1), (5, 1), (6, 1), (7, 1)] 3
  -- row 10: row 8 + row 9 ==> 0 ≤ -1
  , .integerCut [(8, 1), (9, 1)] 1
  , .integerContradiction 10
  ]

theorem k4_3_cert_checks : verifyCertificate k4_3Formula k4_3Cert = true := by
  decide

theorem k4_3_unsat : ¬ ∃ x : Nat → Bool, SatisfiesFormula k4_3Formula x :=
  unified_certificate_sound k4_3Formula k4_3Cert k4_3_cert_checks

/-! ## Example 3: Pigeonhole Principle PHP_2^3 via Divisor-2 Gomory–Chvátal Cuts

Variables:
- `p_{i,j}` for pigeon `i ∈ {0, 1, 2}` and hole `j ∈ {0, 1}`:
  - `0 = p_{0,0}`, `1 = p_{0,1}`
  - `2 = p_{1,0}`, `3 = p_{1,1}`
  - `4 = p_{2,0}`, `5 = p_{2,1}`
- `6 = const_0`, `7 = const_1` via `(6, 6, 7)`
- `8..13` = hole pairwise slack variables `s_{i1,i2,j}`
-/

def php2_3Formula : Formula1in3 :=
  [ (6, 6, 7)    -- c0: const_0 = 0, const_1 = 1
  , (0, 1, 6)    -- c1: pigeon 0: p_{0,0} + p_{0,1} + const_0 = 1
  , (2, 3, 6)    -- c2: pigeon 1: p_{1,0} + p_{1,1} + const_0 = 1
  , (4, 5, 6)    -- c3: pigeon 2: p_{2,0} + p_{2,1} + const_0 = 1
  , (0, 2, 8)    -- c4: hole 0 pair (0,1): p_{0,0} + p_{1,0} + s0 ≤ 1
  , (0, 4, 9)    -- c5: hole 0 pair (0,2): p_{0,0} + p_{2,0} + s1 ≤ 1
  , (2, 4, 10)   -- c6: hole 0 pair (1,2): p_{1,0} + p_{2,0} + s2 ≤ 1
  , (1, 3, 11)   -- c7: hole 1 pair (0,1): p_{0,1} + p_{1,1} + s3 ≤ 1
  , (1, 5, 12)   -- c8: hole 1 pair (0,2): p_{0,1} + p_{2,1} + s4 ≤ 1
  , (3, 5, 13)   -- c9: hole 1 pair (1,2): p_{1,1} + p_{2,1} + s5 ≤ 1
  ]

def php2_3Cert : List UnifiedProofStep :=
  [ -- Derive const_0 ≤ 0 via (6, 6, 7): 2*x6 + x7 ≤ 1, -x7 ≤ 0 ==> 2*x6 ≤ 1 ==> (div 2) x6 ≤ 0
    .integerClauseLift 0 true   -- row 0: 2*x6 + x7 ≤ 1
  , .integerBoxBound 7 false    -- row 1: -x7 ≤ 0
  , .integerCut [(0, 1), (1, 1)] 2  -- row 2: x6 ≤ 0 (const_0 = 0!)
    -- Lift 3 pigeon lower bounds and eliminate const_0 via row 2
  , .integerClauseLift 1 false  -- row 3: -p00 - p01 - x6 ≤ -1
  , .integerClauseLift 2 false  -- row 4: -p10 - p11 - x6 ≤ -1
  , .integerClauseLift 3 false  -- row 5: -p20 - p21 - x6 ≤ -1
  , .integerCut [(3, 1), (2, 1)] 1  -- row 6: -p00 - p01 ≤ -1
  , .integerCut [(4, 1), (2, 1)] 1  -- row 7: -p10 - p11 ≤ -1
  , .integerCut [(5, 1), (2, 1)] 1  -- row 8: -p20 - p21 ≤ -1
    -- Hole 0 pairwise edges (eliminate slacks 8, 9, 10 via box_lo)
  , .integerClauseLift 4 true   -- row 9
  , .integerClauseLift 5 true   -- row 10
  , .integerClauseLift 6 true   -- row 11
  , .integerBoxBound 8 false    -- row 12
  , .integerBoxBound 9 false    -- row 13
  , .integerBoxBound 10 false   -- row 14
  , .integerCut [(9, 1), (12, 1)] 1   -- row 15: p00 + p10 ≤ 1
  , .integerCut [(10, 1), (13, 1)] 1  -- row 16: p00 + p20 ≤ 1
  , .integerCut [(11, 1), (14, 1)] 1  -- row 17: p10 + p20 ≤ 1
    -- Hole 0 divisor-2 Gomory-Chvatal clique cut: 2*(p00+p10+p20) ≤ 3 ==> p00+p10+p20 ≤ 1
  , .integerCut [(15, 1), (16, 1), (17, 1)] 2  -- row 18: p00 + p10 + p20 ≤ 1
    -- Hole 1 pairwise edges (eliminate slacks 11, 12, 13 via box_lo)
  , .integerClauseLift 7 true   -- row 19
  , .integerClauseLift 8 true   -- row 20
  , .integerClauseLift 9 true   -- row 21
  , .integerBoxBound 11 false   -- row 22
  , .integerBoxBound 12 false   -- row 23
  , .integerBoxBound 13 false   -- row 24
  , .integerCut [(19, 1), (22, 1)] 1  -- row 25: p01 + p11 ≤ 1
  , .integerCut [(20, 1), (23, 1)] 1  -- row 26: p01 + p21 ≤ 1
  , .integerCut [(21, 1), (24, 1)] 1  -- row 27: p11 + p21 ≤ 1
    -- Hole 1 divisor-2 Gomory-Chvatal clique cut: 2*(p01+p11+p21) ≤ 3 ==> p01+p11+p21 ≤ 1
  , .integerCut [(25, 1), (26, 1), (27, 1)] 2  -- row 28: p01 + p11 + p21 ≤ 1
    -- Global counting cancellation: (Hole 0 + Hole 1) + (Pigeon 0 + Pigeon 1 + Pigeon 2) ==> 0 ≤ -1
  , .integerCut [(18, 1), (28, 1), (6, 1), (7, 1), (8, 1)] 1  -- row 29: 0 ≤ -1
  , .integerContradiction 29
  ]

theorem php2_3_cert_checks : verifyCertificate php2_3Formula php2_3Cert = true := by
  decide

theorem php2_3_unsat : ¬ ∃ x : Nat → Bool, SatisfiesFormula php2_3Formula x :=
  unified_certificate_sound php2_3Formula php2_3Cert php2_3_cert_checks

end Monotone1in3.Examples
