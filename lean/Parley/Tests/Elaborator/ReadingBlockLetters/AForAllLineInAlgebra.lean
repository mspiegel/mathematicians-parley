module

public import Tactics

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAlgebra

theorem a_for_all_line_in_algebra (hH1 : ∀ x : ℝ, x ^ 2 = 2 * x) :
    (∀ y : ℝ, y ^ 2 + 1 = 2 * y + 1) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y ^ 2 + 1 = 2 * y + 1 := by
    intro y
    -- 1.1. algebra, from H1
    have s1_1 : y ^ 2 + 1 = 2 * y + 1 := by linear_combination (norm := parley_norm) (hH1 y)
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAlgebra
