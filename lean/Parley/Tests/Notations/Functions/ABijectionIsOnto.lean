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

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ABijectionIsOnto

theorem a_bijection_is_onto {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (f : α → β) (hH3 : Set.MapsTo f A B ∧ Set.InjOn f A ∧ Set.SurjOn f A B) :
    (Set.MapsTo f A B ∧ Set.SurjOn f A B) := by
  -- 1. def:one-to-one-onto, from H3
  exact (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := f) hH3.1)).mp hH3).2

end Parley.Tests.Notations.Functions.ABijectionIsOnto
