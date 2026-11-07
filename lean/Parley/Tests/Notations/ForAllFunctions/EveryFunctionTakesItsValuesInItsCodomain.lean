module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/for-all-functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.ForAllFunctions.EveryFunctionTakesItsValuesInItsCodomain

theorem every_function_takes_its_values_in_its_codomain {α : Type*} (X : Set α) (Y : Set α) (a : α) (hH3 : a ∈ X) :
    (∀ f : α → α, Set.MapsTo f X Y → f a ∈ Y) := by
  -- 1. proof
  have s1 : ∀ f : α → α, Set.MapsTo f X Y → f a ∈ Y := by
    intro f hK1
    -- 1.1. mun:function-value x := a, from H3
    have s1_1 : f a ∈ Y := by exact (Parley.Items.Stdlib.Functions.mun_function_value (D := X) (E := Y) (f := f) (x := a) hH3 (by parley_set_side))
    all_goals exact s1_1
  all_goals exact s1

end Parley.Tests.Notations.ForAllFunctions.EveryFunctionTakesItsValuesInItsCodomain
