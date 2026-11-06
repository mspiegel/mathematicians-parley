module

public import Tactics
public import Mathlib.Data.Rat.Init
public import Parley.Proofs.Setmm.RationalClosure.RationalProduct
public import Parley.Proofs.Setmm.RationalClosure.RationalReciprocal

/-! Written from proofs/setmm/rational-closure.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RationalClosure.RationalQuotient

theorem rational_quotient (A : ℚ) (B : ℚ) (hH3 : B ≠ 0) :
    True := by
  -- 1. thm:rational-reciprocal A := B, from H3
  -- 2. thm:rational-product B := 1/B, from 1
  -- 3. substitute
  all_goals parley_side

end Parley.Proofs.Setmm.RationalClosure.RationalQuotient
