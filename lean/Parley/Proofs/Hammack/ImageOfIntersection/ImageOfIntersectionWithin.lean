module

public import LeanBridges
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/image-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ImageOfIntersection.ImageOfIntersectionWithin

theorem image_of_intersection_within {α : Type*} (A : Set α) (B : Set α) (f : α → α) (hH3 : Set.MapsTo f A B) (W : Set α) (hH4 : W ⊆ A) (X : Set α) (hH5 : X ⊆ A) :
    f '' (W ∩ X) ⊆ f '' W ∩ f '' X := by
  -- 1. proof
  have s1 : ∀ s ∈ W ∩ X, s ∈ A := by
    intro s hK1
    -- 1.1. def:intersection u := s, Y := W, Z := X, from K1
    have s1_1a : s ∈ W := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1; parley_side)
    have s1_1b : s ∈ X := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2; parley_side)
    -- 1.2. mun:in-subset X := W, Y := A, u := s, from H4, 1.1
    have s1_2 : s ∈ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := W) (Y := A) (u := s) (by parley_side) (by parley_side)); parley_side)
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : W ∩ X ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := W ∩ X) (Y := A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := W ∩ X) (Y := A))).mpr (by parley_side); parley_side)
  -- 3. proof
  have s3 : ∀ y ∈ f '' (W ∩ X), y ∈ f '' W ∩ f '' X := by
    intro y hK2
    -- 3.1. obtain s: def:image u := y, Y := W ∩ X, from K2, 2
    obtain ⟨s, s3_1b⟩ := ((Parley.Items.Stdlib.Functions.def_image (X := A) (Y := W ∩ X) (f := f) (u := y) (W := _) (by parley_side) (by parley_side))).mp (by parley_side)
    -- 3.2. def:intersection u := s, Y := W, Z := X, from 3.1
    have s3_2a : s ∈ W := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).1; parley_side)
    have s3_2b : s ∈ X := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := W) (Z := X) (u := s))).mp (by parley_side)).2; parley_side)
    -- 3.3. mun:value-in-image Y := W, from H4, 3.2
    have s3_3 : f s ∈ f '' W := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := W) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    -- 3.4. mun:value-in-image Y := X, from H5, 3.2
    have s3_4 : f s ∈ f '' X := by first | exact (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Functions.mun_value_in_image (X := A) (Y := X) (f := f) (s := s) (W := _) (by parley_side) (by parley_side) (by parley_side)); parley_side)
    -- 3.5. substitute y = f(s) (line 3.1) into line 3.3
    have s3_5 : y ∈ f '' W := by parley_subst_at s3_1b s3_3
    -- 3.6. substitute y = f(s) (line 3.1) into line 3.4
    have s3_6 : y ∈ f '' X := by parley_subst_at s3_1b s3_4
    -- 3.7. def:intersection u := y, Y := f[W], Z := f[X], from 3.5, 3.6
    have s3_7 : y ∈ f '' W ∩ f '' X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := f '' W) (Z := f '' X) (u := y))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := f '' W) (Z := f '' X) (u := y))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 4. def:subset, from 3
  have s4 : f '' (W ∩ X) ⊆ f '' W ∩ f '' X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (W ∩ X)) (Y := f '' W ∩ f '' X))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := f '' (W ∩ X)) (Y := f '' W ∩ f '' X))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.ImageOfIntersection.ImageOfIntersectionWithin
