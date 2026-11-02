module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-inside-a-larger-set.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceInsideALargerSet.DifferenceInsideALargerSet

theorem difference_inside_a_larger_set {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) :
    A \ B = (C \ B) ∩ A := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ B, t ∈ (C \ B) ∩ A := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := B, from K1
    have s1_1a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1; parley_side)
    have s1_1b : ¬ t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2; parley_side)
    -- 1.2. mun:in-subset X := A, Y := C, u := t, from H4, 1.1
    have s1_2 : t ∈ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)); parley_side)
    -- 1.3. def:difference u := t, Y := C, Z := B, from 1.1, 1.2
    have s1_3 : t ∈ C \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_side); parley_side)
    -- 1.4. def:intersection u := t, Y := C ∖ B, Z := A, from 1.1, 1.3
    have s1_4 : t ∈ (C \ B) ∩ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : A \ B ⊆ (C \ B) ∩ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := (C \ B) ∩ A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := (C \ B) ∩ A))).mpr (by parley_side); parley_side)
  -- 3. proof
  have s3 : ∀ t ∈ (C \ B) ∩ A, t ∈ A \ B := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := C ∖ B, Z := A, from K2
    have s3_1a : t ∈ C \ B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).1; parley_side)
    have s3_1b : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp (by parley_side)).2; parley_side)
    -- 3.2. def:difference u := t, Y := C, Z := B, from 3.1
    have s3_2a : t ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).1; parley_side)
    have s3_2b : ¬ t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp (by parley_side)).2; parley_side)
    -- 3.3. def:difference u := t, Y := A, Z := B, from 3.1, 3.2
    have s3_3 : t ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 4. def:subset, from 3
  have s4 : (C \ B) ∩ A ⊆ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (C \ B) ∩ A) (Y := A \ B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (C \ B) ∩ A) (Y := A \ B))).mpr (by parley_side); parley_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A \ B = (C \ B) ∩ A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.DifferenceInsideALargerSet.DifferenceInsideALargerSet
