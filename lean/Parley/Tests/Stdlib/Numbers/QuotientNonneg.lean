module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.QuotientNonneg

theorem quotient_nonneg (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y > 0) :
    x / y ≥ 0 := by
  -- 1. mun:numbers-quotient-nonneg, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := x) (y := y) hH3 hH4)

end Parley.Tests.Stdlib.Numbers.QuotientNonneg
