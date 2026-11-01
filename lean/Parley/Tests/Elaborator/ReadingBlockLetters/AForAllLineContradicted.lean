module

public import Parley.Library

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted

theorem a_for_all_line_contradicted (H1 : ∀ x : ℝ, x ^ 2 + 1 ≠ 0) :
    (∀ y : ℝ, y ^ 2 + 1 ≠ 0) := by
  -- 1. proof
  have s1 : ∀ y : ℝ, y ^ 2 + 1 ≠ 0 := by
    intro y
    -- 1.1. contradiction
    have s1_1 : y ^ 2 + 1 ≠ 0 := by
      by_contra hc_S
      have S : y ^ 2 + 1 = 0 := by parley_suppose hc_S
      -- 1.1.1. restate S
      have s1_1_1 : y ^ 2 + 1 = 0 := by parley_side
      parley_side
    parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineContradicted
