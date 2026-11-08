module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductThatIsZero

theorem a_product_that_is_zero (x : ℝ) (y : ℝ) (hH3 : x * y = 0) :
    (x = 0 ∨ y = 0) := by
  -- 1. mun:zero-product, from H3
  exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := x) (y := y))).mp hH3

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductThatIsZero
