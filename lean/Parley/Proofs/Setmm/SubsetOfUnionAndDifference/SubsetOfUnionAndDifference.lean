module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-union-and-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfUnionAndDifference.SubsetOfUnionAndDifference

theorem subset_of_union_and_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ⊆ B ∪ C ↔ A \ B ⊆ C) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ∪ C ↔ A \ B ⊆ C := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ u ∈ A \ B, u ∈ C := by
        intro u hK1
        -- 1.1. def:difference Y := A, Z := B, from K1
        have s1_1a : u ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).1; parley_side)
        have s1_1b : ¬ u ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_side)).2; parley_side)
        -- 1.2. mun:in-subset X := A, Y := B ∪ C, from D1, 1.1
        have s1_2 : u ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) (by parley_side) (by parley_side)); parley_side)
        -- 1.3. def:union Y := B, Z := C, from 1.2
        have s1_3 : u ∈ B ∨ u ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp (by parley_side); parley_side)
        -- 1.4. cases, from 1.3
        have s1_4 : u ∈ C := by
          rcases s1_3 with hC1 | hC2
          · skip
            -- 1.4.1. restate 1.1
            have s1_4_1 : ¬ u ∈ B := by parley_side
            all_goals parley_side
          · skip
            -- 1.4.2. restate C2
            have s1_4_2 : u ∈ C := by parley_side
            all_goals parley_side
        all_goals parley_side
      -- 2. def:subset X := A ∖ B, Y := C, from 1
      have s2 : A \ B ⊆ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := C))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := C))).mpr (by parley_side); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 3. proof
      have s3 : ∀ u ∈ A, u ∈ B ∪ C := by
        intro u hK2
        -- 3.1. axi:excluded-middle P := u ∈ B
        have s3_1 : u ∈ B ∨ ¬ u ∈ B := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)); parley_side)
        -- 3.2. cases, from 3.1
        have s3_2 : u ∈ B ∪ C := by
          rcases s3_1 with hC1 | hC2
          · skip
            -- 3.2.1. mun:or-left, from C1
            have s3_2_1 : u ∈ B ∨ u ∈ C := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) (by parley_side)); parley_side)
            -- 3.2.2. def:union Y := B, Z := C, from 3.2.1
            have s3_2_2 : u ∈ B ∪ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr (by parley_side); parley_side)
            all_goals parley_side
          · skip
            -- 3.2.3. def:difference Y := A, Z := B, from C2, K2
            have s3_2_3 : u ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_side); parley_side)
            -- 3.2.4. mun:in-subset X := A ∖ B, Y := C, from D2, 3.2.3
            have s3_2_4 : u ∈ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) (by parley_side) (by parley_side)); parley_side)
            -- 3.2.5. mun:or-right, from 3.2.4
            have s3_2_5 : u ∈ B ∨ u ∈ C := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) (by parley_side)); parley_side)
            -- 3.2.6. def:union Y := B, Z := C, from 3.2.5
            have s3_2_6 : u ∈ B ∪ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr (by parley_side); parley_side)
            all_goals parley_side
        all_goals parley_side
      -- 4. def:subset X := A, Y := B ∪ C, from 3
      have s4 : A ⊆ B ∪ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr (by parley_side); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.SubsetOfUnionAndDifference.SubsetOfUnionAndDifference
