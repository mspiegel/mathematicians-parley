module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/union-and-difference-equal.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.UnionAndDifferenceEqual.UnionAndDifferenceEqual

theorem union_and_difference_equal {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) (hH5 : A ∩ B = ∅) :
    (A ∪ B = C ↔ C \ A = B) := by
  -- the theorem. both directions
  have sThm : A ∪ B = C ↔ C \ A = B := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ u ∈ C \ A, u ∈ B := by
        intro u hK1
        -- 1.1. def:difference Y := C, Z := A, from K1
        have s1_1a : u ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).1; parley_side)
        have s1_1b : ¬ u ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mp (by parley_side)).2; parley_side)
        -- 1.2. substitute A ∪ B = C (D1) into line 1.1
        have s1_2 : u ∈ A ∪ B := by parley_subst_at hD1 s1_1a
        -- 1.3. def:union Y := A, Z := B, from 1.2
        have s1_3 : u ∈ A ∨ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side); parley_side)
        -- 1.4. cases, from 1.3
        have s1_4 : u ∈ B := by
          rcases s1_3 with hC1 | hC2
          · skip
            -- 1.4.1. restate 1.1
            have s1_4_1 : ¬ u ∈ A := by parley_side
            all_goals parley_side
          · skip
            -- 1.4.2. restate C2
            have s1_4_2 : u ∈ B := by parley_side
            all_goals parley_side
        all_goals parley_side
      -- 2. def:subset X := C ∖ A, Y := B, from 1
      have s2 : C \ A ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := C \ A) (Y := B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := C \ A) (Y := B))).mpr (by parley_side); parley_side)
      -- 3. proof
      have s3 : ∀ u ∈ B, u ∈ C \ A := by
        intro u hK2
        -- 3.1. mun:in-union-right Y := A, Z := B, from K2
        have s3_1 : u ∈ A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)); parley_side)
        -- 3.2. substitute A ∪ B = C (D1) into line 3.1
        have s3_2 : u ∈ C := by parley_subst_at hD1 s3_1
        -- 3.3. contradiction
        have s3_3 : ¬ u ∈ A := by
          by_contra hc_hS
          have hS : u ∈ A := by parley_suppose hc_hS
          -- 3.3.1. mun:disjoint-member Y := A, Z := B, from H5, S
          have s3_3_1 : ¬ u ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := u) (by parley_side) (by parley_side)); parley_side)
          all_goals parley_side
        -- 3.4. def:difference Y := C, Z := A, from 3.2, 3.3
        have s3_4 : u ∈ C \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mpr (by parley_side); parley_side)
        all_goals parley_side
      -- 4. def:subset X := B, Y := C ∖ A, from 3
      have s4 : B ⊆ C \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := C \ A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := B) (Y := C \ A))).mpr (by parley_side); parley_side)
      -- 5. mun:subset-antisymmetric X := C ∖ A, Y := B, from 2, 4
      have s5 : C \ A = B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := C \ A) (Y := B) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
    · skip
      intro hD2
      -- 6. mun:difference-subset X := C, Y := A
      have s6 : C \ A ⊆ C := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := C) (Y := A)); parley_side)
      -- 7. substitute C ∖ A = B (D2) into line 6
      have s7 : B ⊆ C := by parley_subst_at hD2 s6
      -- 8. mun:union-subset X := A, Y := B, Z := C, from H4, 7
      have s8 : A ∪ B ⊆ C := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := A) (Y := B) (Z := C) (by parley_side) (by parley_side)); parley_side)
      -- 9. proof
      have s9 : ∀ u ∈ C, u ∈ A ∪ B := by
        intro u hK3
        -- 9.1. axi:excluded-middle P := u ∈ A
        have s9_1 : u ∈ A ∨ ¬ u ∈ A := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)); parley_side)
        -- 9.2. cases, from 9.1
        have s9_2 : u ∈ A ∪ B := by
          rcases s9_1 with hC3 | hC4
          · skip
            -- 9.2.1. mun:in-union-left Y := A, Z := B, from C3
            have s9_2_1 : u ∈ A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)); parley_side)
            all_goals parley_side
          · skip
            -- 9.2.2. def:difference Y := C, Z := A, from C4, K3
            have s9_2_2 : u ∈ C \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := A) (u := u))).mpr (by parley_side); parley_side)
            -- 9.2.3. substitute C ∖ A = B (D2) into line 9.2.2
            have s9_2_3 : u ∈ B := by parley_subst_at hD2 s9_2_2
            -- 9.2.4. mun:in-union-right Y := A, Z := B, from 9.2.3
            have s9_2_4 : u ∈ A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)); parley_side)
            all_goals parley_side
        all_goals parley_side
      -- 10. def:subset X := C, Y := A ∪ B, from 9
      have s10 : C ⊆ A ∪ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := A ∪ B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := A ∪ B))).mpr (by parley_side); parley_side)
      -- 11. mun:subset-antisymmetric X := A ∪ B, Y := C, from 8, 10
      have s11 : A ∪ B = C := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B) (Y := C) (by parley_side) (by parley_side)); parley_side)
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.UnionAndDifferenceEqual.UnionAndDifferenceEqual
