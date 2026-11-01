module

public import Parley.Library

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.AMultiplierOverTheDivisor

theorem a_multiplier_over_the_divisor (x : ℝ) (y : ℝ) (H3 : y = 1) (H4 : x + 3 ≠ 0) :
    x * y / (x + 3) + 1 = x / (x + 3) + y := by
  -- 1. algebra, from H3
  have r54_1 : x + 3 ≠ 0 := by parley_side
  have s1 : x * y / (x + 3) + 1 = x / (x + 3) + y := by linear_combination (norm := parley_field) ((-3) / ((x + 3))) * H3
  all_goals parley_side

end Parley.Tests.Elaborator.Divisors.AMultiplierOverTheDivisor
