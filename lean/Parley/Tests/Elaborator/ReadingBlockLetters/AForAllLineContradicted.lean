module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted

theorem a_for_all_line_contradicted (hH1 : ∀ x : ℝ, x ^ 2 + 1 ≠ 0) :
    (∀ y : ℝ, y ^ 2 + 1 ≠ 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y ^ 2 + 1 ≠ 0 := by
    intro y
    -- 1.1. contradiction
    have s1_1 : y ^ 2 + 1 ≠ 0 := by
      by_contra hc_hS
      have hS : y ^ 2 + 1 = 0 := by parley_suppose hc_hS
      -- 1.1.1. restate S
      have s1_1_1 : y ^ 2 + 1 = 0 := by parley_side
      all_goals parley_side
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted
