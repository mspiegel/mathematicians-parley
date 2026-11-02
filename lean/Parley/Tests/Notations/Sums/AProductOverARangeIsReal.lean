module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from tests/notations/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Sums.AProductOverARangeIsReal

theorem a_product_over_a_range_is_real (n : ℕ) (hH1 : 0 < n) (t : ℤ → ℝ) :
    True := by
  -- 1. mun:product-real a := 1, b := n
  all_goals parley_side

end Parley.Tests.Notations.Sums.AProductOverARangeIsReal
