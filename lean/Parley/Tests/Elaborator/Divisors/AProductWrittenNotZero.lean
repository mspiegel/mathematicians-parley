module

public import Parley.Library

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.AProductWrittenNotZero

theorem a_product_written_not_zero (x : ℝ) (y : ℝ) (hH3 : x * y ≠ 0) :
    (2 * x * y + 3) / (x * y) = 2 + 3 / (x * y) := by
  -- 1. algebra
  have r8_1 : x * y ≠ 0 := by parley_side
  have s1 : (2 * x * y + 3) / (x * y) = 2 + 3 / (x * y) := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.Divisors.AProductWrittenNotZero
