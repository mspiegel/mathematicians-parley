module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/records-products-gcds-preimages.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductIsReal

theorem a_product_is_real (n : ℤ) (hH1 : 0 < n) (t : ℤ → ℝ) :
    True := by
  -- 1. mun:product-real a := 1, b := n
  all_goals parley_side

end Parley.Tests.Elaborator.RecordsProductsGcdsPreimages.AProductIsReal
