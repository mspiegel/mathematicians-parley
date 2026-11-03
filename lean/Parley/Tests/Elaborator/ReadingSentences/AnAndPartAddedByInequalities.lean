module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAddedByInequalities

theorem an_and_part_added_by_inequalities (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : a = 1 ∧ b > 0) (hH5 : c > 0) :
    b + c > 0 := by
  -- 1. inequalities, from H4, H5
  have s1 : b + c > 0 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAddedByInequalities
