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

/-! Written from tests/notations/for-all-functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.ForAllFunctions.EveryFunctionTakesItsValuesInItsCodomain

theorem every_function_takes_its_values_in_its_codomain {α β : Type*} [Nonempty α] [Nonempty β] (X : Set α) (Y : Set β) (a : α) (hH3 : a ∈ X) :
    (∀ f : α → β, Set.MapsTo f X Y → f a ∈ Y) := by
  -- 1. proof
  intro f hK1
  -- 1.1. mun:function-value x := a, from H3
  exact (Parley.Items.Stdlib.Functions.mun_function_value (D := X) (E := Y) (f := f) (x := a) hH3 hK1)

end Parley.Tests.Notations.ForAllFunctions.EveryFunctionTakesItsValuesInItsCodomain
