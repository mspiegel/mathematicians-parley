module

public import ArithTactics
public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/complement-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ComplementOfIntersection.ComplementOfIntersection

set_option maxHeartbeats 600000 in
theorem complement_of_intersection {α : Type*} (U : Set α) (A : Set α) (B : Set α) (hH4 : A ⊆ U) (hH5 : B ⊆ U) :
    U \ (A ∩ B) = U \ A ∪ U \ B := by
  -- 1. proof
  have s1 : ∀ t ∈ U \ (A ∩ B), t ∈ U \ A ∪ U \ B := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := U, Z := A ∩ B, from K1
    have s1_1a : t ∈ U := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s1_1b : ¬ t ∈ A ∩ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. axi:excluded-middle P := t ∈ A
    have s1_2 : t ∈ A ∨ ¬ t ∈ A := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ A))
    -- 1.3. cases, from 1.2
    have s1_3 : t ∈ U \ A ∪ U \ B := by
      rcases s1_2 with hC1 | hC2
      · skip
        -- 1.3.1. contradiction
        have s1_3_1 : ¬ t ∈ B := by
          by_contra hc_hS1
          have hS1 : t ∈ B := by parley_suppose hc_hS1
          -- 1.3.1.1. def:intersection u := t, Y := A, Z := B, from C1, S1
          have s1_3_1_1 : t ∈ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
          all_goals parley_set_side
        -- 1.3.2. def:difference u := t, Y := U, Z := B, from 1.1, 1.3.1
        have s1_3_2 : t ∈ U \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
        -- 1.3.3. mun:in-union-right u := t, Y := U ∖ A, Z := U ∖ B, from 1.3.2
        have s1_3_3 : t ∈ U \ A ∪ U \ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := U \ A) (Z := U \ B) (u := t) s1_3_2)
        all_goals parley_set_side
      · skip
        -- 1.3.4. def:difference u := t, Y := U, Z := A, from C2, 1.1
        have s1_3_4 : t ∈ U \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mpr (by parley_set_side); parley_set_side)
        -- 1.3.5. mun:in-union-left u := t, Y := U ∖ A, Z := U ∖ B, from 1.3.4
        have s1_3_5 : t ∈ U \ A ∪ U \ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := U \ A) (Z := U \ B) (u := t) s1_3_4)
        all_goals parley_set_side
    all_goals exact s1_3
  -- 2. def:subset, from 1
  have s2 : U \ (A ∩ B) ⊆ U \ A ∪ U \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := U \ (A ∩ B)) (Y := U \ A ∪ U \ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := U \ (A ∩ B)) (Y := U \ A ∪ U \ B))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ U \ A ∪ U \ B, t ∈ U \ (A ∩ B) := by
    intro t hK2
    -- 3.1. def:union u := t, Y := U ∖ A, Z := U ∖ B, from K2
    have s3_1 : t ∈ U \ A ∨ t ∈ U \ B := by first | exact ((Parley.Items.Stdlib.Sets.def_union (Y := U \ A) (Z := U \ B) (u := t))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_union (Y := U \ A) (Z := U \ B) (u := t))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_union (Y := U \ A) (Z := U \ B) (u := t))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_union (Y := U \ A) (Z := U \ B) (u := t))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := U \ A) (Z := U \ B) (u := t))).mp (by parley_set_side); parley_set_side)
    -- 3.2. cases, from 3.1
    have s3_2 : t ∈ U \ (A ∩ B) := by
      rcases s3_1 with hC3 | hC4
      · skip
        -- 3.2.1. def:difference u := t, Y := U, Z := A, from C3
        have s3_2_1a : t ∈ U := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).1; parley_set_side)
        have s3_2_1b : ¬ t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A) (u := t))).mp (by parley_set_side)).2; parley_set_side)
        -- 3.2.2. contradiction
        have s3_2_2 : ¬ t ∈ A ∩ B := by
          by_contra hc_hS2
          have hS2 : t ∈ A ∩ B := by parley_suppose hc_hS2
          -- 3.2.2.1. def:intersection u := t, Y := A, Z := B, from S2
          have s3_2_2_1 : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
          all_goals parley_set_side
        -- 3.2.3. def:difference u := t, Y := U, Z := A ∩ B, from 3.2.1, 3.2.2
        have s3_2_3 : t ∈ U \ (A ∩ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mpr (by parley_set_side); parley_set_side)
        all_goals parley_set_side
      · skip
        -- 3.2.4. def:difference u := t, Y := U, Z := B, from C4
        have s3_2_4a : t ∈ U := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
        have s3_2_4b : ¬ t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
        -- 3.2.5. contradiction
        have s3_2_5 : ¬ t ∈ A ∩ B := by
          by_contra hc_hS3
          have hS3 : t ∈ A ∩ B := by parley_suppose hc_hS3
          -- 3.2.5.1. def:intersection u := t, Y := A, Z := B, from S3
          have s3_2_5_1 : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
          all_goals parley_set_side
        -- 3.2.6. def:difference u := t, Y := U, Z := A ∩ B, from 3.2.4, 3.2.5
        have s3_2_6 : t ∈ U \ (A ∩ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := U) (Z := A ∩ B) (u := t))).mpr (by parley_set_side); parley_set_side)
        all_goals parley_set_side
    all_goals exact s3_2
  -- 4. def:subset, from 3
  have s4 : U \ A ∪ U \ B ⊆ U \ (A ∩ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := U \ A ∪ U \ B) (Y := U \ (A ∩ B)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := U \ A ∪ U \ B) (Y := U \ (A ∩ B)))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : U \ (A ∩ B) = U \ A ∪ U \ B := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := U \ (A ∩ B)) (Y := U \ A ∪ U \ B) s2 s4)
  all_goals exact s5

end Parley.Proofs.Hammack.ComplementOfIntersection.ComplementOfIntersection
