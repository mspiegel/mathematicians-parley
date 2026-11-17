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

namespace Parley.Tests.Notations.Functions.AnOntoFunctionHasItsValues

theorem an_onto_function_has_its_values {α β : Type*} [Nonempty α] [Nonempty β] (A : Set α) (B : Set β) (f : α → β) (hH3 : Set.MapsTo f A B ∧ Set.SurjOn f A B) (x : α) (hH4 : x ∈ A) :
    f x ∈ B := by
  -- 1. mun:function-value, from H4
  exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) hH4 hH3.1)

end Parley.Tests.Notations.Functions.AnOntoFunctionHasItsValues
