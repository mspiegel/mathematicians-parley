module

public import LeanBridges
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/image-of-part.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ImageOfPart.ImageOfPart

theorem image_of_part {α : Type*} (A : Set α) (B : Set α) (F : α → α) (hH3 : Set.MapsTo F A B) (X : Set α) (hH4 : X ⊆ A) :
    F '' X ⊆ F '' A := by
  -- 1. proof
  have s1 : ∀ u ∈ F '' X, u ∈ F '' A := by
    intro u hK1
    -- 1.1. obtain s: def:image Y := X, from H4, K1
    obtain ⟨s, s1_1a, s1_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := X) (f := F) (u := u) (W := Set.univ) (by parley_side) (by parley_side))).mp (by parley_side)
    -- 1.2. mun:in-subset, from H4, 1.1
    have s1_2 : s ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := X) (Y := A) (u := s) (by parley_side) (by parley_side)); parley_side)
    -- 1.3. mun:value-in-image Y := A, from 1.2
    have r25_1 : A ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_self (X := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_self (X := A)); parley_side)
    have s1_3 : F s ∈ F '' A := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := A) (f := F) (s := s) (W := Set.univ) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    -- 1.4. substitute u = F(s) (line 1.1) into line 1.3
    have s1_4 : u ∈ F '' A := by parley_subst_at s1_1b s1_3
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : F '' X ⊆ F '' A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := F '' X) (Y := F '' A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := F '' X) (Y := F '' A))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.ImageOfPart.ImageOfPart
