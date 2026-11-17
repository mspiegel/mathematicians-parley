module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-phrase-with-a-where-part.proof by parley build lean. -/

public section

namespace Parley.Items.Tests.Elaborator.APhraseWithAWherePart

theorem def_clique {α : Type*} [Nonempty α] (E : Set (Set α)) (W : Set α) (n : ℕ) :
    ((n : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ↔ ((n : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) :=
  Iff.rfl

theorem def_rising_run (S : Set ℝ) (a : ℝ → ℝ) (r : ℕ) :
    ((r : ℕ) : ℕ∞) ≤ S.encard ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) ↔ ((r : ℕ) : ℕ∞) ≤ S.encard ∧ (∀ i ∈ S, ∀ j ∈ S, i < j → a i < a j) :=
  Iff.rfl

end Parley.Items.Tests.Elaborator.APhraseWithAWherePart
