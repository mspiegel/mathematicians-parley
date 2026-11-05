module

public import Tactics

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.Ramsey

theorem def_clique {α : Type*} (E : Set (Set α)) (W : Set α) (n : ℕ) :
    ((n : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ↔ ((n : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.Ramsey
