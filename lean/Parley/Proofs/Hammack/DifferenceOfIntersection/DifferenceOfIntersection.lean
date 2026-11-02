module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/difference-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceOfIntersection.DifferenceOfIntersection

theorem difference_of_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A \ (B ∩ C) = A \ B ∪ A \ C := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ (B ∩ C), t ∈ A \ B ∪ A \ C := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := B ∩ C, from K1
    have s1_1a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).1; parley_side)
    have s1_1b : ¬ t ∈ B ∩ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp (by parley_side)).2; parley_side)
    -- 1.2. axi:excluded-middle P := t ∈ B
    have s1_2 : t ∈ B ∨ ¬ t ∈ B := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B)); parley_side)
    -- 1.3. cases, from 1.2
    have s1_3 : t ∈ A \ B ∪ A \ C := by
      rcases s1_2 with hC1 | hC2
      · skip
        -- 1.3.1. contradiction
        have s1_3_1 : ¬ t ∈ C := by
          by_contra hc_hS1
          have hS1 : t ∈ C := by parley_suppose hc_hS1
          -- 1.3.1.1. def:intersection u := t, Y := B, Z := C, from C1, S1
          have s1_3_1_1 : t ∈ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr (by parley_side); parley_side)
          all_goals parley_side
        -- 1.3.2. def:difference u := t, Y := A, Z := C, from 1.1, 1.3.1
        have s1_3_2 : t ∈ A \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_side); parley_side)
        -- 1.3.3. mun:in-union-right u := t, Y := A ∖ B, Z := A ∖ C, from 1.3.2
        have s1_3_3 : t ∈ A \ B ∪ A \ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)); parley_side)
        all_goals parley_side
      · skip
        -- 1.3.4. def:difference u := t, Y := A, Z := B, from C2, 1.1
        have s1_3_4 : t ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_side); parley_side)
        -- 1.3.5. mun:in-union-left u := t, Y := A ∖ B, Z := A ∖ C, from 1.3.4
        have s1_3_5 : t ∈ A \ B ∪ A \ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) (by parley_side)); parley_side)
        all_goals parley_side
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : A \ (B ∩ C) ⊆ A \ B ∪ A \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C))).mpr (by parley_side); parley_side)
  -- 3. proof
  have s3 : ∀ t ∈ A \ B ∪ A \ C, t ∈ A \ (B ∩ C) := by
    intro t hK2
    -- 3.1. def:union u := t, Y := A ∖ B, Z := A ∖ C, from K2
    have s3_1 : t ∈ A \ B ∨ t ∈ A \ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side); parley_side)
    -- 3.2. cases, from 3.1
    have s3_2 : t ∈ A \ (B ∩ C) := by
      rcases s3_1 with hC3 | hC4
      · skip
        -- 3.2.1. def:difference u := t, Y := A, Z := B, from C3
        have s3_2_1a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1; parley_side)
        have s3_2_1b : ¬ t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2; parley_side)
        -- 3.2.2. contradiction
        have s3_2_2 : ¬ t ∈ B ∩ C := by
          by_contra hc_hS2
          have hS2 : t ∈ B ∩ C := by parley_suppose hc_hS2
          -- 3.2.2.1. def:intersection u := t, Y := B, Z := C, from S2
          have s3_2_2_1 : t ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side); parley_side)
          all_goals parley_side
        -- 3.2.3. def:difference u := t, Y := A, Z := B ∩ C, from 3.2.1, 3.2.2
        have s3_2_3 : t ∈ A \ (B ∩ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mpr (by parley_side); parley_side)
        all_goals parley_side
      · skip
        -- 3.2.4. def:difference u := t, Y := A, Z := C, from C4
        have s3_2_4a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).1; parley_side)
        have s3_2_4b : ¬ t ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).2; parley_side)
        -- 3.2.5. contradiction
        have s3_2_5 : ¬ t ∈ B ∩ C := by
          by_contra hc_hS3
          have hS3 : t ∈ B ∩ C := by parley_suppose hc_hS3
          -- 3.2.5.1. def:intersection u := t, Y := B, Z := C, from S3
          have s3_2_5_1 : t ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (by parley_side); parley_side)
          all_goals parley_side
        -- 3.2.6. def:difference u := t, Y := A, Z := B ∩ C, from 3.2.4, 3.2.5
        have s3_2_6 : t ∈ A \ (B ∩ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mpr (by parley_side); parley_side)
        all_goals parley_side
    all_goals parley_side
  -- 4. def:subset, from 3
  have s4 : A \ B ∪ A \ C ⊆ A \ (B ∩ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B ∪ A \ C) (Y := A \ (B ∩ C)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B ∪ A \ C) (Y := A \ (B ∩ C)))).mpr (by parley_side); parley_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A \ (B ∩ C) = A \ B ∪ A \ C := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.DifferenceOfIntersection.DifferenceOfIntersection
