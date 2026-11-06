module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductThatIsZero

theorem a_product_that_is_zero (x : ℝ) (y : ℝ) (hH3 : x * y = 0) :
    (x = 0 ∨ y = 0) := by
  -- 1. mun:zero-product, from H3
  have s1 : x = 0 ∨ y = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductThatIsZero
