module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/size-of-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeOfDifference.PartAndRest

theorem part_and_rest {α : Type*} (A : Set α) (B : Set α) (hH3 : B ⊆ A) :
    B ∪ A \ B = A := by
  -- 1. mun:difference-subset X := A, Y := B
  have s1 : A \ B ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := A) (Y := B)); parley_side)
  -- 2. mun:union-subset X := B, Y := A ∖ B, Z := A, from H3, 1
  have s2 : B ∪ A \ B ⊆ A := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := B) (Y := A \ B) (Z := A) (by parley_side) (by parley_side)); parley_side)
  -- 3. proof
  have s3 : ∀ u ∈ A, u ∈ B ∪ A \ B := by
    intro u hK
    -- 3.1. axi:excluded-middle P := u ∈ B
    have s3_1 : u ∈ B ∨ ¬ u ∈ B := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)); parley_side)
    -- 3.2. cases, from 3.1
    have s3_2 : u ∈ B ∪ A \ B := by
      rcases s3_1 with hC1 | hC2
      · skip
        -- 3.2.1. mun:in-union-left Y := B, Z := A ∖ B, from C1
        have s3_2_1 : u ∈ B ∪ A \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := A \ B) (u := u) (by parley_side)); parley_side)
        all_goals parley_side
      · skip
        -- 3.2.2. def:difference Y := A, Z := B, from C2, K
        have s3_2_2 : u ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_side); parley_side)
        -- 3.2.3. mun:in-union-right Y := B, Z := A ∖ B, from 3.2.2
        have s3_2_3 : u ∈ B ∪ A \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A \ B) (u := u) (by parley_side)); parley_side)
        all_goals parley_side
    all_goals parley_side
  -- 4. def:subset X := A, Y := B ∪ (A ∖ B), from 3
  have s4 : A ⊆ B ∪ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A \ B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A \ B))).mpr (by parley_side); parley_side)
  -- 5. mun:subset-antisymmetric X := B ∪ (A ∖ B), Y := A, from 2, 4
  have s5 : B ∪ A \ B = A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B ∪ A \ B) (Y := A) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.SizeOfDifference.PartAndRest
