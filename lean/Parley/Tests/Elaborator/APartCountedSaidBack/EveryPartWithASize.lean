module

public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-part-counted-said-back.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APartCountedSaidBack.EveryPartWithASize

theorem every_part_with_a_size {α : Type*} (X : Set α) (hH2 : ∀ W ∈ 𝒫 X, W.encard ≤ ((2 : ℕ) : ℕ∞)) :
    (∀ W ∈ 𝒫 X, W.encard ≤ ((2 : ℕ) : ℕ∞)) := by
  -- 1. restate H2
  exact hH2

end Parley.Tests.Elaborator.APartCountedSaidBack.EveryPartWithASize
