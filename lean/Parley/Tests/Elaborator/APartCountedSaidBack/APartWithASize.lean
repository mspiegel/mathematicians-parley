module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/a-part-counted-said-back.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APartCountedSaidBack.APartWithASize

theorem a_part_with_a_size {α : Type*} (X : Set α) (hH2 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard) :
    (∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard) := by
  -- 1. restate H2
  have s1 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard := by parley_set_side
  all_goals parley_set_side

end Parley.Tests.Elaborator.APartCountedSaidBack.APartWithASize
