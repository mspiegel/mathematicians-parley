module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ProductNonneg

theorem product_nonneg (x : ℝ) (y : ℝ) (hH3 : x ≥ 0) (hH4 : y ≥ 0) :
    x * y ≥ 0 := by
  -- 1. mun:numbers-product-nonneg, from H3, H4
  have s1 : x * y ≥ 0 := by linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x) (y := y) (by parley_side) (by parley_side))]
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.ProductNonneg
