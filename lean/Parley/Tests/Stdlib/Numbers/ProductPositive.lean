module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ProductPositive

theorem product_positive (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    x * y > 0 := by
  -- 1. mun:numbers-product-positive, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_product_positive (x := x) (y := y) (by parley_side) (by parley_side))

end Parley.Tests.Stdlib.Numbers.ProductPositive
