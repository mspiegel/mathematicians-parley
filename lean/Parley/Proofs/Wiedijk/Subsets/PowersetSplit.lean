module

public import SetTactics
public import SubstTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Data.Set.Operations
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Functions
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/wiedijk/subsets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Subsets.PowersetSplit

set_option maxHeartbeats 600000 in
theorem powerset_split {α : Type*} (X : Set α) (a : α) (hH2 : a ∈ X) :
    𝒫 X = 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
  -- 1. proof
  have s1 : ∀ V ∈ 𝒫 X, V ∈ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
    intro V hK1
    -- 1.1. def:powerset S := V, from K1
    have s1_1 : V ⊆ X := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := V))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := V))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := V))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := V))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := V))).mp (by parley_set_side); parley_set_side)
    -- 1.2. axi:excluded-middle P := a ∈ V
    have s1_2 : a ∈ V ∨ ¬ a ∈ V := by first | exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ V)) | exact ((Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ V))).symm | simpa using (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ V)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ V)) | (have h := (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := a ∈ V)); parley_set_side)
    -- 1.3. cases, from 1.2
    have s1_3 : V ∈ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
      rcases s1_2 with hC1 | hC2
      · skip
        -- 1.3.1. mun:difference-shrinks, from 1.1
        have s1_3_1 : V \ ({a} : Set α) ⊆ X \ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := V) (Z := ({a} : Set α)) s1_1) | exact ((Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := V) (Z := ({a} : Set α)) s1_1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := V) (Z := ({a} : Set α)) s1_1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := V) (Z := ({a} : Set α)) s1_1) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_shrinks (X := X) (Y := V) (Z := ({a} : Set α)) s1_1); parley_set_side)
        -- 1.3.2. def:powerset S := V ∖ {a}, from 1.3.1
        have s1_3_2 : V \ ({a} : Set α) ∈ 𝒫 (X \ ({a} : Set α)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := V \ ({a} : Set α)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := V \ ({a} : Set α)))).mpr (by parley_set_side); parley_set_side)
        -- 1.3.3. mun:added-element-in-image Y := 𝒫(X ∖ {a}), s := V ∖ {a}, from 1.3.2
        have s1_3_3 : V \ ({a} : Set α) ∪ ({a} : Set α) ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by first | exact (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := 𝒫 (X \ ({a} : Set α))) (s := V \ ({a} : Set α)) (a := a) s1_3_2) | exact ((Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := 𝒫 (X \ ({a} : Set α))) (s := V \ ({a} : Set α)) (a := a) s1_3_2)).symm | simpa using (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := 𝒫 (X \ ({a} : Set α))) (s := V \ ({a} : Set α)) (a := a) s1_3_2) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := 𝒫 (X \ ({a} : Set α))) (s := V \ ({a} : Set α)) (a := a) s1_3_2) | (have h := (Parley.Items.Stdlib.Functions.mun_added_element_in_image (Y := 𝒫 (X \ ({a} : Set α))) (s := V \ ({a} : Set α)) (a := a) s1_3_2); parley_set_side)
        -- 1.3.4. substitute
        have s1_3_4 : V ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by
          have c1 : V \ ({a} : Set α) ∪ ({a} : Set α) = V := by first | exact (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := V) (a := a) hC1) | exact ((Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := V) (a := a) hC1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := V) (a := a) hC1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := V) (a := a) hC1) | (have h := (Parley.Items.Stdlib.Sets.mun_remove_and_restore (Y := V) (a := a) hC1); parley_set_side)
          have row1 : V ∈ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by parley_subst_at c1 s1_3_3
          exact row1
        -- 1.3.5. mun:in-union-right, from 1.3.4
        have s1_3_5 : V ∈ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_4) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_4) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_4); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 1.3.6. mun:subset-into-difference, from C2, 1.1
        have s1_3_6 : V ⊆ X \ ({a} : Set α) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := V) (a := a) s1_1 hC2) | exact ((Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := V) (a := a) s1_1 hC2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := V) (a := a) s1_1 hC2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := V) (a := a) s1_1 hC2) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_into_difference (X := X) (Y := V) (a := a) s1_1 hC2); parley_set_side)
        -- 1.3.7. def:powerset S := V, from 1.3.6
        have s1_3_7 : V ∈ 𝒫 (X \ ({a} : Set α)) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := V))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := V))).mpr (by parley_set_side); parley_set_side)
        -- 1.3.8. mun:in-union-left, from 1.3.7
        have s1_3_8 : V ∈ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_7) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_7) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := 𝒫 (X \ ({a} : Set α))) (Z := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (u := V) s1_3_7); parley_set_side)
        all_goals parley_set_side
    all_goals exact s1_3
  -- 2. def:subset, from 1
  have s2 : 𝒫 X ⊆ 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))))).mpr (by parley_set_side); parley_set_side)
  -- 3. mun:difference-subset
  have s3 : X \ ({a} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α))) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α)))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α))) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α))) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := X) (Y := ({a} : Set α))); parley_set_side)
  -- 4. mun:powerset-monotone, from 3
  have s4 : 𝒫 (X \ ({a} : Set α)) ⊆ 𝒫 X := by first | exact (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := X) (Y := X \ ({a} : Set α)) s3) | exact ((Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := X) (Y := X \ ({a} : Set α)) s3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := X) (Y := X \ ({a} : Set α)) s3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := X) (Y := X \ ({a} : Set α)) s3) | (have h := (Parley.Items.Stdlib.Sets.mun_powerset_monotone (X := X) (Y := X \ ({a} : Set α)) s3); parley_set_side)
  -- 5. proof
  have s5 : ∀ S ∈ 𝒫 (X \ ({a} : Set α)), S ∪ ({a} : Set α) ∈ 𝒫 X := by
    intro S hK2
    -- 5.1. def:powerset, from K2
    have s5_1 : S ⊆ X \ ({a} : Set α) := by first | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X \ ({a} : Set α)) (S := S))).mp (by parley_set_side); parley_set_side)
    -- 5.2. mun:subset-transitive, from 3, 5.1
    have s5_2 : S ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := X \ ({a} : Set α)) (Z := X) s5_1 s3) | exact ((Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := X \ ({a} : Set α)) (Z := X) s5_1 s3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := X \ ({a} : Set α)) (Z := X) s5_1 s3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := X \ ({a} : Set α)) (Z := X) s5_1 s3) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_transitive (X := S) (Y := X \ ({a} : Set α)) (Z := X) s5_1 s3); parley_set_side)
    -- 5.3. mun:singleton-subset, from H2
    have s5_3 : ({a} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2) | exact ((Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2) | (have h := (Parley.Items.Stdlib.Sets.mun_singleton_subset (X := X) (a := a) hH2); parley_set_side)
    -- 5.4. mun:union-subset, from 5.2, 5.3
    have s5_4 : S ∪ ({a} : Set α) ⊆ X := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := S) (Y := ({a} : Set α)) (Z := X) s5_2 s5_3) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := S) (Y := ({a} : Set α)) (Z := X) s5_2 s5_3)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := S) (Y := ({a} : Set α)) (Z := X) s5_2 s5_3) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := S) (Y := ({a} : Set α)) (Z := X) s5_2 s5_3) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := S) (Y := ({a} : Set α)) (Z := X) s5_2 s5_3); parley_set_side)
    -- 5.5. def:powerset S := S ∪ {a}, from 5.4
    have s5_5 : S ∪ ({a} : Set α) ∈ 𝒫 X := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S ∪ ({a} : Set α)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_powerset (A := X) (S := S ∪ ({a} : Set α)))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s5_5
  -- 6. mun:added-elements-stay-inside Y := 𝒫(X ∖ {a}), Z := 𝒫X, from 5
  have s6 : (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) ⊆ 𝒫 X := by first | exact (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 X) (a := a) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 X) (a := a) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 X) (a := a) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 X) (a := a) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Functions.mun_added_elements_stay_inside (Y := 𝒫 (X \ ({a} : Set α))) (Z := 𝒫 X) (a := a) (by parley_set_side)); parley_set_side)
  -- 7. mun:union-subset, from 4, 6
  have s7 : 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) ⊆ 𝒫 X := by first | exact (Parley.Items.Stdlib.Sets.mun_union_subset (X := 𝒫 (X \ ({a} : Set α))) (Y := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (Z := 𝒫 X) s4 s6) | exact ((Parley.Items.Stdlib.Sets.mun_union_subset (X := 𝒫 (X \ ({a} : Set α))) (Y := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (Z := 𝒫 X) s4 s6)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_subset (X := 𝒫 (X \ ({a} : Set α))) (Y := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (Z := 𝒫 X) s4 s6) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_subset (X := 𝒫 (X \ ({a} : Set α))) (Y := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (Z := 𝒫 X) s4 s6) | (have h := (Parley.Items.Stdlib.Sets.mun_union_subset (X := 𝒫 (X \ ({a} : Set α))) (Y := (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) (Z := 𝒫 X) s4 s6); parley_set_side)
  -- 8. mun:subset-antisymmetric, from 2, 7
  have s8 : 𝒫 X = 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α))) := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2 s7) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2 s7)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2 s7) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2 s7) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := 𝒫 X) (Y := 𝒫 (X \ ({a} : Set α)) ∪ (fun S : Set α => S ∪ ({a} : Set α)) '' (𝒫 (X \ ({a} : Set α)))) s2 s7); parley_set_side)
  all_goals exact s8

end Parley.Proofs.Wiedijk.Subsets.PowersetSplit
