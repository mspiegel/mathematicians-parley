module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-type-a-line-states.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet

theorem into_the_empty_set {α : Type*} (A : Set α) (F : α → α) (hH2 : Set.MapsTo F A ∅) :
    (∀ t ∈ A, F t ∈ (∅ : Set α)) := by
  -- 1. mun:function-value f := F
  have s1 : ∀ t ∈ A, F t ∈ (∅ : Set α) := by intro t h_t; (first | exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := ∅) (f := F) (x := t) (by parley_set_side) (by parley_set_side)); parley_set_side))
  all_goals exact s1

end Parley.Tests.Elaborator.ATypeALineStates.IntoTheEmptySet
