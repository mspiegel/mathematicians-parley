module

public import Parley.Library

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.ADivisorSharingAFactor

theorem a_divisor_sharing_a_factor (x : ℝ) (y : ℝ) (z : ℝ) (H4 : y ^ 2 = 9) (H5 : y - 3 ≠ 0) :
    (x * y ^ 2 - 2 * y ^ 2 - z) / (y - 3) = (9 * x - z - 18) / (y - 3) := by
  -- 1. algebra, from H4
  have r83_1 : y - 3 ≠ 0 := by parley_side
  have s1 : (x * y ^ 2 - 2 * y ^ 2 - z) / (y - 3) = (9 * x - z - 18) / (y - 3) := by linear_combination (norm := parley_field) ((x * y - 3 * x - 2 * y + 6) / (y ^ 2 - 6 * y + 9)) * H4
  parley_side

end Parley.Tests.Elaborator.Divisors.ADivisorSharingAFactor
