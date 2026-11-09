module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/difference-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceOfIntersection.DifferenceOfIntersection

set_option maxHeartbeats 600000 in
theorem difference_of_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A \ (B ∩ C) = A \ B ∪ A \ C := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ (B ∩ C), t ∈ A \ B ∪ A \ C := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := B ∩ C, from K1
    have s1_1a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ B ∩ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mp hK1).2
    -- 1.2. axi:excluded-middle P := t ∈ B
    have s1_2 : t ∈ B ∨ ¬ t ∈ B := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ B))
    -- 1.3. cases, from 1.2
    rcases s1_2 with hC1 | hC2
    · skip
      -- 1.3.1. contradiction
      have s1_3_1 : ¬ t ∈ C := by
        intro hS1
        -- 1.3.1.1. def:intersection u := t, Y := B, Z := C, from C1, S1
        have s1_3_1_1 : t ∈ B ∩ C := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr (by parley_set_side)
        exact s1_1b s1_3_1_1
      -- 1.3.2. def:difference u := t, Y := A, Z := C, from 1.1, 1.3.1
      have s1_3_2 : t ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_set_side)
      -- 1.3.3. mun:in-union-right u := t, Y := A ∖ B, Z := A ∖ C, from 1.3.2
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ B) (Z := A \ C) (u := t) s1_3_2)
    · skip
      -- 1.3.4. def:difference u := t, Y := A, Z := B, from C2, 1.1
      have s1_3_4 : t ∈ A \ B := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side)
      -- 1.3.5. mun:in-union-left u := t, Y := A ∖ B, Z := A ∖ C, from 1.3.4
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ B) (Z := A \ C) (u := t) s1_3_4)
  -- 2. def:subset, from 1
  have s2 : A \ (B ∩ C) ⊆ A \ B ∪ A \ C := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ A \ B ∪ A \ C, t ∈ A \ (B ∩ C) := by
    intro t hK2
    -- 3.1. def:union u := t, Y := A ∖ B, Z := A ∖ C, from K2
    have s3_1 : t ∈ A \ B ∨ t ∈ A \ C := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := A \ B) (Z := A \ C) (u := t))).mp hK2
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC3 | hC4
    · skip
      -- 3.2.1. def:difference u := t, Y := A, Z := B, from C3
      have s3_2_1a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp hC3).1
      have s3_2_1b : ¬ t ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp hC3).2
      -- 3.2.2. contradiction
      have s3_2_2 : ¬ t ∈ B ∩ C := by
        intro hS2
        -- 3.2.2.1. def:intersection u := t, Y := B, Z := C, from S2
        have s3_2_2_1 : t ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp hS2).1
        exact s3_2_1b s3_2_2_1
      -- 3.2.3. def:difference u := t, Y := A, Z := B ∩ C, from 3.2.1, 3.2.2
      exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mpr (by parley_set_side)
    · skip
      -- 3.2.4. def:difference u := t, Y := A, Z := C, from C4
      have s3_2_4a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hC4).1
      have s3_2_4b : ¬ t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hC4).2
      -- 3.2.5. contradiction
      have s3_2_5 : ¬ t ∈ B ∩ C := by
        intro hS3
        -- 3.2.5.1. def:intersection u := t, Y := B, Z := C, from S3
        have s3_2_5_1 : t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp hS3).2
        exact s3_2_4b s3_2_5_1
      -- 3.2.6. def:difference u := t, Y := A, Z := B ∩ C, from 3.2.4, 3.2.5
      exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∩ C) (u := t))).mpr (by parley_set_side)
  -- 4. def:subset, from 3
  have s4 : A \ B ∪ A \ C ⊆ A \ (B ∩ C) := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B ∪ A \ C) (Y := A \ (B ∩ C)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∩ C)) (Y := A \ B ∪ A \ C) s2 s4)

end Parley.Proofs.Hammack.DifferenceOfIntersection.DifferenceOfIntersection
