module

public import Tactics

/-! Written from tests/elaborator/reading-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingSentences.AnAndPartObtainedFrom

theorem an_and_part_obtained_from (a : ℝ) (b : ℤ) (hH3 : a = 1 ∧ (∃ k : ℤ, b = 2 * k)) :
    (∃ j : ℤ, b = 2 * j) := by
  -- 1. obtain k from H3
  obtain ⟨k, s1⟩ := hH3.2
  -- 2. exhibit, from 1
  have s2 : ∃ j : ℤ, b = 2 * j := ⟨k, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingSentences.AnAndPartObtainedFrom
