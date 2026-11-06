module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.AMultiplierOfTwoTerms

theorem a_multiplier_of_two_terms (x : ℝ) (y : ℝ) (hH3 : y = 1) :
    x ^ 2 * y - x * y + 2 = x ^ 2 - x + 2 := by
  -- 1. algebra, from H3
  have s1 : x ^ 2 * y - x * y + 2 = x ^ 2 - x + 2 := by linear_combination (norm := parley_norm) (x ^ 2 - x) * hH3
  all_goals exact s1

end Parley.Tests.Elaborator.Combinations.AMultiplierOfTwoTerms
