module

public import LeanBridges

/-! Written from tests/elaborator/a-part-counted-said-back.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APartCountedSaidBack.APartWithASize

theorem a_part_with_a_size {α : Type*} (X : Set α) (hH2 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard) :
    (∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard) := by
  -- 1. restate H2
  have s1 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.APartCountedSaidBack.APartWithASize
