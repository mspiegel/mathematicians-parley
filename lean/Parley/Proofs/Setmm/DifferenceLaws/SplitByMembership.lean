module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.SplitByMembership

set_option maxHeartbeats 400000 in
theorem split_by_membership {α : Type*} (A : Set α) (B : Set α) :
    A ∩ B ∪ A \ B = A := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ B ∪ A \ B, u ∈ A := by
    intro u hK1
    -- 1.1. def:union, from K1
    have s1_1 : u ∈ A ∩ B ∨ u ∈ A \ B := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ B) (Z := A \ B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ B) (Z := A \ B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ B) (Z := A \ B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ B) (Z := A \ B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ B) (Z := A \ B) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 1.2. cases, from 1.1
    have s1_2 : u ∈ A := by
      rcases s1_1 with hC1 | hC2
      · skip
        -- 1.2.1. def:intersection, from C1
        have s1_2_1 : u ∈ A ∧ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side); parley_set_side)
        -- 1.2.2. restate 1.2.1
        have s1_2_2 : u ∈ A := by parley_set_side
        all_goals parley_set_side
      · skip
        -- 1.2.3. def:difference, from C2
        have s1_2_3 : u ∈ A ∧ ¬ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side); parley_set_side)
        -- 1.2.4. restate 1.2.3
        have s1_2_4 : u ∈ A := by parley_set_side
        all_goals parley_set_side
    all_goals exact s1_2
  -- 2. def:subset, from 1
  have s2 : A ∩ B ∪ A \ B ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B ∪ A \ B) (Y := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B ∪ A \ B) (Y := A))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ u ∈ A, u ∈ A ∩ B ∪ A \ B := by
    intro u hK2
    -- 3.1. axi:excluded-middle P := u ∈ B
    have s3_1 : u ∈ B ∨ ¬ u ∈ B := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B)); parley_set_side)
    -- 3.2. cases, from 3.1
    have s3_2 : u ∈ A ∩ B ∪ A \ B := by
      rcases s3_1 with hC3 | hC4
      · skip
        -- 3.2.1. join K2, C3
        have s3_2_1 : u ∈ A ∧ u ∈ B := by parley_set_side
        -- 3.2.2. def:intersection, from 3.2.1
        have s3_2_2 : u ∈ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mpr (by parley_set_side); parley_set_side)
        -- 3.2.3. mun:in-union-left, from 3.2.2
        have s3_2_3 : u ∈ A ∩ B ∪ A \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_2) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_2); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 3.2.4. join K2, C4
        have s3_2_4 : u ∈ A ∧ ¬ u ∈ B := by parley_set_side
        -- 3.2.5. def:difference, from 3.2.4
        have s3_2_5 : u ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side); parley_set_side)
        -- 3.2.6. mun:in-union-right, from 3.2.5
        have s3_2_6 : u ∈ A ∩ B ∪ A \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_5) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_5)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_5) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_5) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ B) (Z := A \ B) (u := u) s3_2_5); parley_set_side)
        all_goals parley_set_side
    all_goals exact s3_2
  -- 4. def:subset, from 3
  have s4 : A ⊆ A ∩ B ∪ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∩ B ∪ A \ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∩ B ∪ A \ B))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A ∩ B ∪ A \ B = A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B ∪ A \ B) (Y := A) s2 s4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B ∪ A \ B) (Y := A) s2 s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B ∪ A \ B) (Y := A) s2 s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B ∪ A \ B) (Y := A) s2 s4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ B ∪ A \ B) (Y := A) s2 s4); parley_set_side)
  all_goals exact s5

end Parley.Proofs.Setmm.DifferenceLaws.SplitByMembership
