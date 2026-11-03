module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ProductNonzero

theorem product_nonzero (x : ℝ) (y : ℝ) (hH3 : x ≠ 0) (hH4 : y ≠ 0) :
    x * y ≠ 0 := by
  -- 1. mun:numbers-product-nonzero, from H3, H4
  have s1 : x * y ≠ 0 := by first | exact (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := y) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := y) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonzero (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.ProductNonzero
