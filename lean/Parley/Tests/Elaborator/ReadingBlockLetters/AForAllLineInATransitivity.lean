module

public import Parley.Library

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInATransitivity

theorem a_for_all_line_in_a_transitivity (b : ℝ) (H2 : ∀ x : ℝ, x < x + 1) :
    (∀ y : ℝ, y + 1 < b → y < b) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y + 1 < b → y < b := by
    intro y
    intro A1
    -- 1.1. transitivity, from H2, A1
    have s1_1 : y < b := by linarith
    parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInATransitivity
