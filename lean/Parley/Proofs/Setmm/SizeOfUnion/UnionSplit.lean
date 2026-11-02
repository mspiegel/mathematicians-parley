module

public import Tactics
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/size-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SizeOfUnion.UnionSplit

theorem union_split {α : Type*} (A : Set α) (B : Set α) :
    A ∪ B \ A = A ∪ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∪ B \ A, u ∈ A ∪ B := by
    intro u hK1
    -- 1.1. def:union Y := A, Z := B ∖ A, from K1
    have s1_1 : u ∈ A ∨ u ∈ B \ A := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B \ A) (u := u))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B \ A) (u := u))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B \ A) (u := u))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B \ A) (u := u))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B \ A) (u := u))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B \ A) (u := u))).mp (by parley_side); parley_side)
    -- 1.2. cases, from 1.1
    have s1_2 : u ∈ A ∪ B := by
      rcases s1_1 with hC1 | hC2
      · skip
        -- 1.2.1. mun:in-union-left Y := A, Z := B, from C1
        have s1_2_1 : u ∈ A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_side)); parley_side)
        all_goals parley_side
      · skip
        -- 1.2.2. def:difference Y := B, Z := A, from C2
        have s1_2_2a : u ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).1; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).1; parley_side)
        have s1_2_2b : ¬ u ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).2; simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mp (by parley_side)).2; parley_side)
        -- 1.2.3. mun:in-union-right Y := A, Z := B, from 1.2.2
        have s1_2_3 : u ∈ A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := u) (by parley_side)); parley_side)
        all_goals parley_side
    all_goals parley_side
  -- 2. def:subset X := A ∪ (B ∖ A), Y := A ∪ B, from 1
  have s2 : A ∪ B \ A ⊆ A ∪ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B \ A) (Y := A ∪ B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B \ A) (Y := A ∪ B))).mpr (by parley_side); parley_side)
  -- 3. proof
  have s3 : ∀ u ∈ A ∪ B, u ∈ A ∪ B \ A := by
    intro u hK2
    -- 3.1. def:union Y := A, Z := B, from K2
    have s3_1 : u ∈ A ∨ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := u))).mp (by parley_side); parley_side)
    -- 3.2. axi:excluded-middle P := u ∈ A
    have s3_2 : u ∈ A ∨ ¬ u ∈ A := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ A)); parley_side)
    -- 3.3. cases, from 3.2
    have s3_3 : u ∈ A ∪ B \ A := by
      rcases s3_2 with hC3 | hC4
      · skip
        -- 3.3.1. mun:in-union-left Y := A, Z := B ∖ A, from C3
        have s3_3_1 : u ∈ A ∪ B \ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B \ A) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B \ A) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B \ A) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B \ A) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B \ A) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B \ A) (u := u) (by parley_side)); parley_side)
        all_goals parley_side
      · skip
        -- 3.3.2. mun:disjunctive-syllogism-left, from C4, 3.1
        have s3_3_2 : u ∈ B := by first | exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := u ∈ A) (Q := u ∈ B) (by parley_side) (by parley_side)); parley_side)
        -- 3.3.3. def:difference Y := B, Z := A, from C4, 3.3.2
        have s3_3_3 : u ∈ B \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := u))).mpr (by parley_side); parley_side)
        -- 3.3.4. mun:in-union-right Y := A, Z := B ∖ A, from 3.3.3
        have s3_3_4 : u ∈ A ∪ B \ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B \ A) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B \ A) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B \ A) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B \ A) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B \ A) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B \ A) (u := u) (by parley_side)); parley_side)
        all_goals parley_side
    all_goals parley_side
  -- 4. def:subset X := A ∪ B, Y := A ∪ (B ∖ A), from 3
  have s4 : A ∪ B ⊆ A ∪ B \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B) (Y := A ∪ B \ A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B) (Y := A ∪ B \ A))).mpr (by parley_side); parley_side)
  -- 5. mun:subset-antisymmetric X := A ∪ (B ∖ A), Y := A ∪ B, from 2, 4
  have s5 : A ∪ B \ A = A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B \ A) (Y := A ∪ B) (by parley_side) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B \ A) (Y := A ∪ B) (by parley_side) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B \ A) (Y := A ∪ B) (by parley_side) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B \ A) (Y := A ∪ B) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B \ A) (Y := A ∪ B) (by parley_side) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B \ A) (Y := A ∪ B) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.SizeOfUnion.UnionSplit
