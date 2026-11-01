module

public import Parley.Library

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated

theorem a_for_all_line_instantiated (H1 : ∀ x : ℝ, ∀ z : ℝ, x * z = z * x) :
    (∀ y : ℝ, y * 2 = 2 * y) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y * 2 = 2 * y := by
    intro y
    -- 1.1. instantiate z := 2 in H1
    have s1_1 : y * 2 = 2 * y := by linear_combination (H1 y (2 : ℝ))
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInstantiated
