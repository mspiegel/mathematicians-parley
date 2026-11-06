module

public import ArithTactics
public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-by-double-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetByDoubleDifference.SubsetByDoubleDifference

set_option maxHeartbeats 400000 in
theorem subset_by_double_difference {α : Type*} (A : Set α) (B : Set α) :
    (A ⊆ B ↔ B \ (B \ A) = A) := by
  -- the theorem. both directions
  have sThm : A ⊆ B ↔ B \ (B \ A) = A := by
    constructor
    · skip
      intro hD1
      -- 1. proof
      have s1 : ∀ t ∈ B \ (B \ A), t ∈ A := by
        intro t hK1
        by_contra hc_hS1
        have hS1 : ¬ t ∈ A := by parley_suppose hc_hS1
        -- 1.1. def:difference u := t, Y := B, Z := B ∖ A, from K1
        have s1_1a : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).1; parley_set_side)
        have s1_1b : ¬ t ∈ B \ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp (by parley_set_side)).2; parley_set_side)
        -- 1.2. def:difference u := t, Y := B, Z := A, from S1, 1.1
        have s1_2 : t ∈ B \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mpr (by parley_set_side); parley_set_side)
        -- 1.3. restate 1.1
        have s1_3 : ¬ t ∈ B \ A := by parley_set_side
        all_goals parley_set_side
      -- 2. def:subset, from 1
      have s2 : B \ (B \ A) ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := B \ (B \ A)) (Y := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := B \ (B \ A)) (Y := A))).mpr (by parley_set_side); parley_set_side)
      -- 3. proof
      have s3 : ∀ t ∈ A, t ∈ B \ (B \ A) := by
        intro t hK2
        -- 3.1. mun:in-subset X := A, Y := B, u := t, from D1, K2
        have s3_1 : t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2); parley_set_side)
        -- 3.2. contradiction
        have s3_2 : ¬ t ∈ B \ A := by
          by_contra hc_hS2
          have hS2 : t ∈ B \ A := by parley_suppose hc_hS2
          -- 3.2.1. def:difference u := t, Y := B, Z := A, from S2
          have s3_2_1a : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).1; parley_set_side)
          have s3_2_1b : ¬ t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp (by parley_set_side)).2; parley_set_side)
          -- 3.2.2. restate 3.2.1
          have s3_2_2 : ¬ t ∈ A := by parley_set_side
          all_goals parley_set_side
        -- 3.3. def:difference u := t, Y := B, Z := B ∖ A, from 3.1, 3.2
        have s3_3 : t ∈ B \ (B \ A) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mpr (by parley_set_side); parley_set_side)
        all_goals exact s3_3
      -- 4. def:subset, from 3
      have s4 : A ⊆ B \ (B \ A) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B \ (B \ A)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B \ (B \ A)))).mpr (by parley_set_side); parley_set_side)
      -- 5. mun:subset-antisymmetric, from 2, 4
      have s5 : B \ (B \ A) = A := by first | exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B \ (B \ A)) (Y := A) s2 s4) | exact ((Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B \ (B \ A)) (Y := A) s2 s4)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B \ (B \ A)) (Y := A) s2 s4) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B \ (B \ A)) (Y := A) s2 s4) | (have h := (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B \ (B \ A)) (Y := A) s2 s4); parley_set_side)
      all_goals parley_set_side
    · skip
      intro hD2
      -- 6. mun:difference-subset X := B, Y := B ∖ A
      have s6 : B \ (B \ A) ⊆ B := by first | exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := B \ A)) | exact ((Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := B \ A))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := B \ A)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := B \ A)) | (have h := (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := B \ A)); parley_set_side)
      -- 7. substitute B ∖ (B ∖ A) = A (D2) into line 6
      have s7 : A ⊆ B := by parley_subst_at hD2 s6
      all_goals parley_set_side
  all_goals parley_set_side

end Parley.Proofs.Setmm.SubsetByDoubleDifference.SubsetByDoubleDifference
