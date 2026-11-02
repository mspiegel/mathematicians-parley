module

public import LeanBridges
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AnOntoFunctionHasItsValues

theorem an_onto_function_has_its_values {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B ∧ Set.SurjOn f A B) (x : α) (hH4 : x ∈ A) :
    f x ∈ B := by
  -- 1. mun:function-value, from H4
  have s1 : f x ∈ B := by first | exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := f) (x := x) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Notations.Functions.AnOntoFunctionHasItsValues
