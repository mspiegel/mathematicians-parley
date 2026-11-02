module

public import Tactics

/-! Written from tests/elaborator/an-obtain-from-two-sentences.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnObtainFromTwoSentences.AnObtainFromTwoSentences

theorem an_obtain_from_two_sentences {α : Type*} (A : Set α) (u : α) (hH2 : u ∈ A) (hH3 : ∃ x ∈ A, x = u) :
    (∃ y ∈ A, y = u) := by
  -- 1. join H2, H3
  have s1a : u ∈ A := by parley_side
  have s1b : ∃ x ∈ A, x = u := by parley_side
  -- 2. obtain x from line 1
  obtain ⟨x, s2a, s2b⟩ := s1b
  -- 3. exhibit, from 2
  have s3 : ∃ y ∈ A, y = u := ⟨x, by parley_side, by parley_side⟩
  all_goals parley_side

end Parley.Tests.Elaborator.AnObtainFromTwoSentences.AnObtainFromTwoSentences
