module

public import Tactics

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.ATermWithAFraction

theorem a_term_with_a_fraction (x : ℝ) (y : ℝ) (z : ℝ) (hH4 : 3 + x = 0) :
    1 / 5 * (x * z) + y + 3 / 5 * z = y := by
  -- 1. algebra, from H4
  have s1 : 1 / 5 * (x * z) + y + 3 / 5 * z = y := by linear_combination (norm := parley_norm) ((5 * z) / ((25))) * hH4
  all_goals exact s1

end Parley.Tests.Elaborator.Combinations.ATermWithAFraction
