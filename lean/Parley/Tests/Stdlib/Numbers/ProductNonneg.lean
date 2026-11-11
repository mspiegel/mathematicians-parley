module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ProductNonneg

theorem product_nonneg (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y ≥ 0) :
    x * y ≥ 0 := by
  -- 1. mun:numbers-product-nonneg, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x) (y := y) hH3 hH4)

end Parley.Tests.Stdlib.Numbers.ProductNonneg
