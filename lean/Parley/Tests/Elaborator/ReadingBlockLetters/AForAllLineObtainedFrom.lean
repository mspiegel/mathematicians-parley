module

public import Parley.Library

/-! Written from tests/elaborator/reading-block-letters.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineObtainedFrom

theorem a_for_all_line_obtained_from (hH1 : ∀ x : ℤ, ∃ k : ℤ, x = 2 * k) :
    (∀ y : ℤ, ∃ j : ℤ, y = 2 * j) := by
  -- 1. proof
  have s1 : ∀ y : ℤ, ∃ j : ℤ, y = 2 * j := by
    intro y
    -- 1.1. obtain k from H1
    obtain ⟨k, s1_1⟩ := (hH1 y)
    -- 1.2. exhibit, from 1.1
    have s1_2 : ∃ j : ℤ, y = 2 * j := ⟨k, by parley_side⟩
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingBlockLetters.AForAllLineObtainedFrom
