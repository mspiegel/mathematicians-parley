module

public import SetTactics
public import SubstTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
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
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ t ∈ B \ (B \ A), t ∈ A := by
      intro t hK1
      by_contra hS1
      -- 1.1. def:difference u := t, Y := B, Z := B ∖ A, from K1
      have s1_1a : t ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp hK1).1
      have s1_1b : ¬ t ∈ B \ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mp hK1).2
      -- 1.2. def:difference u := t, Y := B, Z := A, from S1, 1.1
      have s1_2 : t ∈ B \ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mpr (by parley_set_side); parley_set_side)
      -- 1.3. restate 1.1
      have s1_3 : ¬ t ∈ B \ A := by parley_set_side
      exact s1_3 s1_2
    -- 2. def:subset, from 1
    have s2 : B \ (B \ A) ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := B \ (B \ A)) (Y := A))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := B \ (B \ A)) (Y := A))).mpr s1; parley_set_side)
    -- 3. proof
    have s3 : ∀ t ∈ A, t ∈ B \ (B \ A) := by
      intro t hK2
      -- 3.1. mun:in-subset X := A, Y := B, u := t, from D1, K2
      have s3_1 : t ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hD1 hK2)
      -- 3.2. contradiction
      have s3_2 : ¬ t ∈ B \ A := by
        intro hS2
        -- 3.2.1. def:difference u := t, Y := B, Z := A, from S2
        have s3_2_1a : t ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp hS2).1
        have s3_2_1b : ¬ t ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := A) (u := t))).mp hS2).2
        -- 3.2.2. restate 3.2.1
        have s3_2_2 : ¬ t ∈ A := by parley_set_side
        exact s3_2_2 hK2
      -- 3.3. def:difference u := t, Y := B, Z := B ∖ A, from 3.1, 3.2
      first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := B \ A) (u := t))).mpr (by parley_set_side); parley_set_side)
    -- 4. def:subset, from 3
    have s4 : A ⊆ B \ (B \ A) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B \ (B \ A)))).mpr s3 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B \ (B \ A)))).mpr s3; parley_set_side)
    -- 5. mun:subset-antisymmetric, from 2, 4
    exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := B \ (B \ A)) (Y := A) s2 s4)
  · skip
    intro hD2
    -- 6. mun:difference-subset X := B, Y := B ∖ A
    have s6 : B \ (B \ A) ⊆ B := by exact (Parley.Items.Stdlib.Sets.mun_difference_subset (X := B) (Y := B \ A))
    -- 7. substitute B ∖ (B ∖ A) = A (D2) into line 6
    parley_subst_at hD2 s6

end Parley.Proofs.Setmm.SubsetByDoubleDifference.SubsetByDoubleDifference
