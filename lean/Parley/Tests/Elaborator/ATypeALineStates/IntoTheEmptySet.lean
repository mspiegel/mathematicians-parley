module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-type-a-line-states.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet

theorem into_the_empty_set {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (F : α → β) (hH2 : Set.MapsTo F A ∅) :
    (∀ t ∈ A, F t ∈ (∅ : Set β)) := by
  -- 1. mun:function-value f := F
  intro t h_t; (exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) h_t hH2))

end Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet
