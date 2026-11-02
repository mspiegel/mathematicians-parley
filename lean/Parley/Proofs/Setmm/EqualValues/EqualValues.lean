module

public import LeanBridges
public import Parley.Items.Stdlib.Functions

/-! Written from proofs/setmm/equal-values.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.EqualValues.EqualValues

theorem equal_values {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B ∧ Set.InjOn F A) (C : α) (hH4 : C ∈ A) (D : α) (hH5 : D ∈ A) :
    (F C = F D ↔ C = D) := by
  -- 1. def:one-to-one, from H3
  have s1 : ∀ s ∈ A, ∀ t ∈ A, F s = F t → s = t := by first | exact ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_side))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_side))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_side))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_side))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Functions.def_one_to_one (X := A) (Y := B) (f := F) (by parley_side))).mp (by parley_side); parley_side)
  -- 2. both directions
  have s2 : F C = F D ↔ C = D := by
    constructor
    · skip
      intro hD1
      -- 2.1. instantiate s := C, t := D in line 1, from D1, H4, H5
      have s2_1 : C = D := by first | exact (s1 C (by parley_side) D (by parley_side) (by parley_side)) | exact ((s1 C (by parley_side) D (by parley_side) (by parley_side))).symm | simpa using (s1 C (by parley_side) D (by parley_side) (by parley_side)) | exact_mod_cast (s1 C (by parley_side) D (by parley_side) (by parley_side)) | (have h := (s1 C (by parley_side) D (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (s1 C (by parley_side) D (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 2.2. substitute C = D (D2)
      have s2_2 : F C = F D := by parley_subst hD2
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.EqualValues.EqualValues
