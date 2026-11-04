module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/a-part-counted-said-back.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APartCountedSaidBack.EveryPartWithASize

theorem every_part_with_a_size {α : Type*} (X : Set α) (hH2 : ∀ W ∈ 𝒫 X, W.encard ≤ ((2 : ℕ) : ℕ∞)) :
    (∀ W ∈ 𝒫 X, W.encard ≤ ((2 : ℕ) : ℕ∞)) := by
  -- 1. restate H2
  have s1 : ∀ W ∈ 𝒫 X, W.encard ≤ ((2 : ℕ) : ℕ∞) := by intro W h_W; parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.APartCountedSaidBack.EveryPartWithASize
