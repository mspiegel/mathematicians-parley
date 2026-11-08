module

public import SetTactics
public import Tactics
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.TypeStar

/-! Written from tests/elaborator/a-part-counted-said-back.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.APartCountedSaidBack.APartWithASize

theorem a_part_with_a_size {α : Type*} (X : Set α) (hH2 : ∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard) :
    (∃ W ∈ 𝒫 X, ((1 : ℕ) : ℕ∞) ≤ W.encard) := by
  -- 1. restate H2
  parley_set_side

end Parley.Tests.Elaborator.APartCountedSaidBack.APartWithASize
