module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-type-a-line-states.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet

theorem into_the_empty_set {α : Type*} (A : Set α) (F : α → α) (hH2 : Set.MapsTo F A ∅) :
    (∀ t ∈ A, F t ∈ (∅ : Set α)) := by
  -- 1. mun:function-value f := F
  intro t h_t; (exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) h_t hH2))

end Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet
