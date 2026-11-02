module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-a-union-with-a-disjoint-set.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfAUnionWithADisjointSet.SubsetOfAUnionWithADisjointSet

theorem subset_of_a_union_with_a_disjoint_set {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ∩ B = ∅) :
    (A ⊆ B ∪ C ↔ A ⊆ C) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ∪ C ↔ A ⊆ C := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ A, t ∈ C := by
        intro t hK1
        -- 1.1. mun:disjoint-member Y := A, Z := B, from H4, K1
        have s1_1 : ¬ t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) (by parley_side) (by parley_side)); parley_side)
        -- 1.2. mun:in-subset X := A, Y := B ∪ C, u := t, from D1, K1
        have s1_2 : t ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) (by parley_side) (by parley_side)); parley_side)
        -- 1.3. def:union u := t, Y := B, Z := C, from 1.2
        have s1_3 : t ∈ B ∨ t ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side); parley_side)
        -- 1.4. cases, from 1.3
        have s1_4 : t ∈ C := by
          rcases s1_3 with hC1 | hC2
          · skip
            -- 1.4.1. restate C1
            have s1_4_1 : t ∈ B := by parley_side
            all_goals parley_side
          · skip
            all_goals parley_side
        all_goals parley_side
      -- 2. def:subset, from 1
      have s2 : A ⊆ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr (by parley_side); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 3. proof
      have s3 : ∀ t ∈ A, t ∈ B ∪ C := by
        intro t hK2
        -- 3.1. mun:in-subset X := A, Y := C, u := t, from D2, K2
        have s3_1 : t ∈ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) (by parley_side) (by parley_side)); parley_side)
        -- 3.2. mun:in-union-right Y := B, Z := C, from 3.1
        have s3_2 : t ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)); parley_side)
        all_goals parley_side
      -- 4. def:subset, from 3
      have s4 : A ⊆ B ∪ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr (by parley_side); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.SubsetOfAUnionWithADisjointSet.SubsetOfAUnionWithADisjointSet
