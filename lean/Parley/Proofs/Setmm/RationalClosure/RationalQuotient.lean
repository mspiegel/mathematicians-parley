module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
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
  exact trivial

end Parley.Proofs.Setmm.RationalClosure.RationalQuotient
