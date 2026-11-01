module

public import Parley.Library

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartContradicted

theorem an_and_part_contradicted (a : ℝ) (b : ℝ) (H3 : a = 1 ∧ b ≠ 2) :
    (b = 2 → a = 0) := by
  -- 1. proof
  have s1 : b = 2 → a = 0 := by
    intro K1
    -- 1.1. restate K1
    have s1_1 : b = 2 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartContradicted
