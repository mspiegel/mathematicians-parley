module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsQuotient

theorem abs_quotient (x : ℝ) (y : ℝ) (hH3 : y ≠ 0) :
    abs (x / y) = abs x / abs y := by
  -- 1. mun:numbers-abs-quotient, from H3
  exact (Parley.Items.Stdlib.Numbers.mun_abs_quotient (x := x) (y := y) hH3)

end Parley.Tests.Stdlib.Numbers.AbsQuotient
