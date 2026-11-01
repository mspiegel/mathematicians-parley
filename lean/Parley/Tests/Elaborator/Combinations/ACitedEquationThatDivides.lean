module

public import Parley.Library

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.ACitedEquationThatDivides

theorem a_cited_equation_that_divides (x : ℝ) (y : ℝ) (hH3 : (x + y) / 2 = 2) :
    1 / 2 * (x * y) + 1 / 2 * y ^ 2 + y = 3 * y := by
  -- 1. algebra, from H3
  have s1 : 1 / 2 * (x * y) + 1 / 2 * y ^ 2 + y = 3 * y := by linear_combination (norm := parley_norm) ((8 * y) / ((4) * (2))) * hH3
  all_goals parley_side

end Parley.Tests.Elaborator.Combinations.ACitedEquationThatDivides
