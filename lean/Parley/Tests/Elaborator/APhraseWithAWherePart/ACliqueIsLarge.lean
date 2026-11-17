module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Tests.Elaborator.APhraseWithAWherePart

/-! Written from tests/elaborator/a-phrase-with-a-where-part.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APhraseWithAWherePart.ACliqueIsLarge

theorem a_clique_is_large {α : Type*} [Nonempty α] (X : Set α) (E : Set (Set α)) (hH3 : ∀ Y ∈ E, Y ⊆ X) (k : ℤ) (hH4 : 0 < k) (W : Set α) (hH5 : W ⊆ X) (hH6 : (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E)) :
    (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard := by
  -- 1. D1 n := k + 1, from H6
  have s1 : (((k + 1).toNat : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) := hH6
  -- 2. restate 1
  exact s1.1

end Parley.Tests.Elaborator.APhraseWithAWherePart.ACliqueIsLarge
