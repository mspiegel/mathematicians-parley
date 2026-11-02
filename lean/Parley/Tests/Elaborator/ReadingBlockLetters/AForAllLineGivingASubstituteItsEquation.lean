module

public import Tactics

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineGivingASubstituteItsEquation

theorem a_for_all_line_giving_a_substitute_its_equation (hH1 : ∀ x : ℝ, x ^ 2 = x * x) :
    (∀ y : ℝ, y ^ 2 + 1 = y * y + 1) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y ^ 2 + 1 = y * y + 1 := by
    intro y
    -- 1.1. substitute y² = y·y (H1)
    have s1_1 : y ^ 2 + 1 = y * y + 1 := by parley_subst hH1
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineGivingASubstituteItsEquation
