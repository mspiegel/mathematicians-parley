module

public import Tactics
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.TypeStar

/-! Written from proofs/wiedijk/ramsey.proof by parley build lean. -/

public section

namespace Parley.Items.Proofs.Wiedijk.Ramsey

theorem def_clique {α : Type*} (E : Set (Set α)) (W : Set α) (n : ℕ) :
    ((n : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) ↔ ((n : ℕ) : ℕ∞) ≤ W.encard ∧ (∀ Y ∈ 𝒫 W, Y.encard = ((2 : ℕ) : ℕ∞) → Y ∈ E) :=
  Iff.rfl

end Parley.Items.Proofs.Wiedijk.Ramsey
