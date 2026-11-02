module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/disjoint-within-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DisjointWithinDifference.DisjointWithinDifference

theorem disjoint_within_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) :
    (A ∩ B = ∅ ↔ A ⊆ C \ B) := by
  -- the theorem. both directions
  have sThm : A ∩ B = ∅ ↔ A ⊆ C \ B := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ A, t ∈ C \ B := by
        intro t hK
        -- 1.1. mun:in-subset X := A, Y := C, u := t, from H4, K
        have s1_1 : t ∈ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)); parley_side)
        -- 1.2. mun:disjoint-member Y := A, Z := B, u := t, from D1, K
        have s1_2 : ¬ t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)); parley_side)
        -- 1.3. def:difference u := t, Y := C, Z := B, from 1.1, 1.2
        have s1_3 : t ∈ C \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_side); parley_side)
        all_goals parley_side
      -- 2. def:subset X := A, Y := C ∖ B, from 1
      have s2 : A ⊆ C \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mpr (by parley_side); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 3. def:subset X := A, Y := C ∖ B, from D2
      have s3 : ∀ t ∈ A, t ∈ C \ B := by first | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp (by parley_side); parley_side)
      -- 4. proof
      have s4 : ∀ s ∈ A, ¬ s ∈ B := by
        intro s hK
        -- 4.1. instantiate t := s in line 3, from K
        have s4_1 : s ∈ C \ B := by first | exact (s3 s (by parley_side)) | exact ((s3 s (by parley_side))).symm | simpa using (s3 s (by parley_side)) | exact_mod_cast (s3 s (by parley_side)) | (have h := (s3 s (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (s3 s (by parley_side)); parley_side)
        -- 4.2. def:difference u := s, Y := C, Z := B, from 4.1
        have s4_2 : s ∈ C ∧ ¬ s ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp (by parley_side); parley_side)
        -- 4.3. restate 4.2
        have s4_3 : ¬ s ∈ B := by parley_side
        all_goals parley_side
      -- 5. calculation
      have s5 : A ∩ B = ∅ := by
        calc A ∩ B = B ∩ A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B)); parley_side)
          _ = ∅ := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.DisjointWithinDifference.DisjointWithinDifference
