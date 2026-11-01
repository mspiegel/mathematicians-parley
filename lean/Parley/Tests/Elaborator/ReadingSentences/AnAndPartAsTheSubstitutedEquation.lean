module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsTheSubstitutedEquation

theorem an_and_part_as_the_substituted_equation (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b = 2) :
    a + b = a + 2 := by
  -- 1. substitute b = 2 (H3)
  have s1 : a + b = a + 2 := by parley_subst hH3.2
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsTheSubstitutedEquation
