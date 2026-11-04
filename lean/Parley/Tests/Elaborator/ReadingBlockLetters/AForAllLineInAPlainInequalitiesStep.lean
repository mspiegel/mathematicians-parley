module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAPlainInequalitiesStep

theorem a_for_all_line_in_a_plain_inequalities_step (hH1 : ∀ x : ℝ, ¬ x ^ 2 < 0) :
    (∀ y : ℝ, y ^ 2 ≥ 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y ^ 2 ≥ 0 := by
    intro y
    -- 1.1. inequalities, from H1
    have s1_1 : y ^ 2 ≥ 0 := by have := (hH1 y); parley_order
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineInAPlainInequalitiesStep
