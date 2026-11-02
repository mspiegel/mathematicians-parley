module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.IntersectionWithDifference

theorem intersection_with_difference {α : Type*} (A : Set α) (B : Set α) :
    A ∩ (A \ B) = A \ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ (A \ B), u ∈ A \ B := by
    intro u hK1
    -- 1.1. def:intersection, from K1
    have s1_1 : u ∈ A ∧ u ∈ A \ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 1.2. restate 1.1
    have s1_2 : u ∈ A \ B := by parley_set_side
    all_goals parley_set_side
  -- 2. def:subset, from 1
  have s2 : A ∩ (A \ B) ⊆ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ (A \ B)) (Y := A \ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ (A \ B)) (Y := A \ B))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ u ∈ A \ B, u ∈ A ∩ (A \ B) := by
    intro u hK2
    -- 3.1. def:difference, from K2
    have s3_1 : u ∈ A ∧ ¬ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 3.2. join K2, 3.1
    have s3_2 : u ∈ A ∧ u ∈ A \ B := by parley_set_side
    -- 3.3. def:intersection, from 3.2
    have s3_3 : u ∈ A ∩ (A \ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := A \ B) (u := u))).mpr (by parley_set_side); parley_set_side)
    all_goals parley_set_side
  -- 4. def:subset, from 3
  have s4 : A \ B ⊆ A ∩ (A \ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := A ∩ (A \ B)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := A ∩ (A \ B)))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : A ∩ (A \ B) = A \ B := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (A \ B)) (Y := A \ B) (by parley_set_side) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (A \ B)) (Y := A \ B) (by parley_set_side) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (A \ B)) (Y := A \ B) (by parley_set_side) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (A \ B)) (Y := A \ B) (by parley_set_side) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (A \ B)) (Y := A \ B) (by parley_set_side) (by parley_set_side)); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Setmm.DifferenceLaws.IntersectionWithDifference
