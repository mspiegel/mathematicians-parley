module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AnOntoFunctionHasItsValues

theorem an_onto_function_has_its_values {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B ∧ Set.SurjOn f A B) (x : α) (hH4 : x ∈ A) :
    f x ∈ B := by
  -- 1. mun:function-value, from H4
  have s1 : f x ∈ B := by first | exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) hH4 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) hH4 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) hH4 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) hH4 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) hH4 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Functions.AnOntoFunctionHasItsValues
