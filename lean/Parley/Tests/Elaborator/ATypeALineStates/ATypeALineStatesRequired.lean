module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Functions

/-! Written from tests/elaborator/a-type-a-line-states.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ATypeALineStates.ATypeALineStatesRequired

theorem a_type_a_line_states_required {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : True) (hH4 : Set.MapsTo F A B) (t : α) (hH5 : t ∈ A) :
    F t ∈ B := by
  -- 1. mun:function-value f := F, from H5
  have r24_1 : Set.MapsTo F A B := by parley_set_side
  have s1 : F t ∈ B := by first | exact (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := F) (x := t) hH5 (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := F) (x := t) hH5 (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := F) (x := t) hH5 (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := F) (x := t) hH5 (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_function_value (D := A) (E := B) (f := F) (x := t) hH5 (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ATypeALineStates.ATypeALineStatesRequired
