module

public import SetTactics
public import Tactics
public import Parley.Items.Tests.Elaborator.APhraseWithAWherePart

/-! Written from tests/elaborator/a-phrase-with-a-where-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseWithAWherePart.ACliqueIsLarge

theorem a_clique_is_large {α : Type*} (X : Set α) (E : Set (Set α)) (hH3 : ∀ Y ∈ E, Y ⊆ X) (k : ℕ) (hH4 : 0 < k) (W : Set α) (hH5 : W ⊆ X) (hH6 : ((k + 1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) :
    ((k + 1 : ℕ) : ℕ∞) ≤ W.encard := by
  -- 1. D1 n := k + 1, from H6
  have s1 : ((k + 1 : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) := by parley_set_side
  -- 2. restate 1
  have s2 : ((k + 1 : ℕ) : ℕ∞) ≤ W.encard := by parley_set_side
  all_goals exact s2

end Parley.Tests.Elaborator.APhraseWithAWherePart.ACliqueIsLarge
