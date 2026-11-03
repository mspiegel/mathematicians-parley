module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.AnOntoFunctionReachesAPoint

theorem an_onto_function_reaches_a_point {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B ∧ Set.SurjOn f A B) (y : α) (hH4 : y ∈ B) :
    (∃ x ∈ A, y = f x) := by
  -- 1. def:onto, from H3
  have s1 : ∀ y ∈ B, ∃ x ∈ A, y = f x := by first | exact (((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Functions.def_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).2; parley_set_side)
  -- 2. instantiate y := y in line 1, from H4
  have s2 : ∃ x ∈ A, y = f x := by first | exact (s1 y (by parley_set_side)) | exact ((s1 y (by parley_set_side))).symm | simpa using (s1 y (by parley_set_side)) | exact_mod_cast (s1 y (by parley_set_side)) | (have h := (s1 y (by parley_set_side)); parley_set_side)
  all_goals exact s2

end Parley.Tests.Notations.Functions.AnOntoFunctionReachesAPoint
