module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/difference-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceOfUnion.DifferenceOfUnion

theorem difference_of_union {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ (B ∪ C), t ∈ (A \ B) ∩ (A \ C) := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := B ∪ C, from K1
    have s1_1a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).1; parley_side)
    have s1_1b : ¬ t ∈ B ∪ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp (by parley_side)).2; parley_side)
    -- 1.2. contradiction
    have s1_2 : ¬ t ∈ B := by
      by_contra hc_hS1
      have hS1 : t ∈ B := by parley_suppose hc_hS1
      -- 1.2.1. mun:in-union-left u := t, Y := B, Z := C, from S1
      have s1_2_1 : t ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) (by parley_side)); parley_side)
      all_goals parley_side
    -- 1.3. contradiction
    have s1_3 : ¬ t ∈ C := by
      by_contra hc_hS2
      have hS2 : t ∈ C := by parley_suppose hc_hS2
      -- 1.3.1. mun:in-union-right u := t, Y := B, Z := C, from S2
      have s1_3_1 : t ∈ B ∪ C := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) (by parley_side)); parley_side)
      all_goals parley_side
    -- 1.4. def:difference u := t, Y := A, Z := B, from 1.1, 1.2
    have s1_4 : t ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_side); parley_side)
    -- 1.5. def:difference u := t, Y := A, Z := C, from 1.1, 1.3
    have s1_5 : t ∈ A \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_side); parley_side)
    -- 1.6. def:intersection u := t, Y := A ∖ B, Z := A ∖ C, from 1.4, 1.5
    have s1_6 : t ∈ (A \ B) ∩ (A \ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : A \ (B ∪ C) ⊆ (A \ B) ∩ (A \ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)))).mpr (by parley_side); parley_side)
  -- 3. proof
  have s3 : ∀ t ∈ (A \ B) ∩ (A \ C), t ∈ A \ (B ∪ C) := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := A ∖ B, Z := A ∖ C, from K2
    have s3_1a : t ∈ A \ B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).1; parley_side)
    have s3_1b : t ∈ A \ C := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp (by parley_side)).2; parley_side)
    -- 3.2. def:difference u := t, Y := A, Z := B, from 3.1
    have s3_2a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).1; parley_side)
    have s3_2b : ¬ t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp (by parley_side)).2; parley_side)
    -- 3.3. def:difference u := t, Y := A, Z := C, from 3.1
    have s3_3 : ¬ t ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_side); parley_side)
    -- 3.4. contradiction
    have s3_4 : ¬ t ∈ B ∪ C := by
      by_contra hc_hS3
      have hS3 : t ∈ B ∪ C := by parley_suppose hc_hS3
      -- 3.4.1. def:union u := t, Y := B, Z := C, from S3
      have s3_4_1 : t ∈ B ∨ t ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp (by parley_side); parley_side)
      -- 3.4.2. mun:disjunctive-syllogism-left P := t ∈ B, Q := t ∈ C, from 3.2, 3.4.1
      have s3_4_2 : t ∈ C := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ B) (Q := t ∈ C) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ B) (Q := t ∈ C) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ B) (Q := t ∈ C) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ B) (Q := t ∈ C) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ B) (Q := t ∈ C) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
    -- 3.5. def:difference u := t, Y := A, Z := B ∪ C, from 3.2, 3.4
    have s3_5 : t ∈ A \ (B ∪ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mpr (by parley_side); parley_side)
    all_goals parley_side
  -- 4. def:subset, from 3
  have s4 : (A \ B) ∩ (A \ C) ⊆ A \ (B ∪ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (A \ B) ∩ (A \ C)) (Y := A \ (B ∪ C)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (A \ B) ∩ (A \ C)) (Y := A \ (B ∪ C)))).mpr (by parley_side); parley_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Hammack.DifferenceOfUnion.DifferenceOfUnion
