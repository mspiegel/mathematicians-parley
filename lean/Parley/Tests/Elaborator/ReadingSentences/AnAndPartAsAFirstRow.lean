module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsAFirstRow

theorem an_and_part_as_a_first_row (a : ℝ) (b : ℝ) (hH3 : a = 1 ∧ b > 0) :
    b + 1 > 1 := by
  -- 1. inequalities
  have s1 : b + 1 > 1 := by parley_order
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartAsAFirstRow
