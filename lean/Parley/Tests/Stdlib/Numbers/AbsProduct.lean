module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsProduct

theorem abs_product (x : ℝ) (y : ℝ) :
    abs (x * y) = abs x * abs y := by
  -- 1. mun:numbers-abs-product
  exact (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y))

end Parley.Tests.Stdlib.Numbers.AbsProduct
