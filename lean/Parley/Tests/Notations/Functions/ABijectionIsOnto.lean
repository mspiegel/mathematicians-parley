module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/notations/functions.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Functions.ABijectionIsOnto

theorem a_bijection_is_onto {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B ∧ Set.InjOn f A ∧ Set.SurjOn f A B) :
    (Set.MapsTo f A B ∧ Set.SurjOn f A B) := by
  -- 1. def:one-to-one-onto, from H3
  have s1 : Set.MapsTo f A B ∧ Set.SurjOn f A B := by first | exact ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one_onto (X := A) (Y := B) (f := f) (by parley_set_side))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Notations.Functions.ABijectionIsOnto
