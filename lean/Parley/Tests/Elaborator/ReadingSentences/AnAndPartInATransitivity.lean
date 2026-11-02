module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartInATransitivity

theorem an_and_part_in_a_transitivity (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = 1 ∧ b ≤ c) (hH5 : c < 0) :
    b < 0 := by
  -- 1. transitivity, from H4, H5
  have s1 : b < 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartInATransitivity
