module

public import Parley.Library

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.AMultiplierOfTwoTerms

theorem a_multiplier_of_two_terms (x : ℝ) (y : ℝ) (hH3 : y = 1) :
    x ^ 2 * y - x * y + 2 = x ^ 2 - x + 2 := by
  -- 1. algebra, from H3
  have s1 : x ^ 2 * y - x * y + 2 = x ^ 2 - x + 2 := by linear_combination (x ^ 2 - x) * hH3
  all_goals parley_side

end Parley.Tests.Elaborator.Combinations.AMultiplierOfTwoTerms
