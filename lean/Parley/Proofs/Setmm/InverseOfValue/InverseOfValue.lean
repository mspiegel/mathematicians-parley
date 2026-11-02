module

public import LeanBridges
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/inverse-of-value.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.InverseOfValue.InverseOfValue

theorem inverse_of_value {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (hH4 : F '' A = B) (C : α) (hH5 : C ∈ A) :
    LeanBridges.Functions.inverse F A (F C) = C := by
  -- 1. mun:inverse-value g := F, y := C, from H3, H5
  have s1 : LeanBridges.Functions.inverse F A (F C) = C := by first | exact (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_inverse_value (X := B) (Y := A) (g := F) (y := C) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.InverseOfValue.InverseOfValue
