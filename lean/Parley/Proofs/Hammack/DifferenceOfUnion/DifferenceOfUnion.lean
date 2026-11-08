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

/-! Written from proofs/hammack/difference-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceOfUnion.DifferenceOfUnion

set_option maxHeartbeats 400000 in
theorem difference_of_union {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A \ (B ∪ C) = (A \ B) ∩ (A \ C) := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ (B ∪ C), t ∈ (A \ B) ∩ (A \ C) := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := B ∪ C, from K1
    have s1_1a : t ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ B ∪ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mp hK1).2
    -- 1.2. contradiction
    have s1_2 : ¬ t ∈ B := by
      intro hS1
      -- 1.2.1. mun:in-union-left u := t, Y := B, Z := C, from S1
      have s1_2_1 : t ∈ B ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) hS1)
      exact s1_1b s1_2_1
    -- 1.3. contradiction
    have s1_3 : ¬ t ∈ C := by
      intro hS2
      -- 1.3.1. mun:in-union-right u := t, Y := B, Z := C, from S2
      have s1_3_1 : t ∈ B ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) hS2)
      exact s1_1b s1_3_1
    -- 1.4. def:difference u := t, Y := A, Z := B, from 1.1, 1.2
    have s1_4 : t ∈ A \ B := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side)
    -- 1.5. def:difference u := t, Y := A, Z := C, from 1.1, 1.3
    have s1_5 : t ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_set_side)
    -- 1.6. def:intersection u := t, Y := A ∖ B, Z := A ∖ C, from 1.4, 1.5
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mpr (by parley_set_side)
  -- 2. def:subset, from 1
  have s2 : A \ (B ∪ C) ⊆ (A \ B) ∩ (A \ C) := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ (A \ B) ∩ (A \ C), t ∈ A \ (B ∪ C) := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := A ∖ B, Z := A ∖ C, from K2
    have s3_1a : t ∈ A \ B := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp hK2).1
    have s3_1b : t ∈ A \ C := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ B) (Z := A \ C) (u := t))).mp hK2).2
    -- 3.2. def:difference u := t, Y := A, Z := B, from 3.1
    have s3_2a : t ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp s3_1a).1
    have s3_2b : ¬ t ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp s3_1a).2
    -- 3.3. def:difference u := t, Y := A, Z := C, from 3.1
    have s3_3 : ¬ t ∈ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp s3_1b).2
    -- 3.4. contradiction
    have s3_4 : ¬ t ∈ B ∪ C := by
      intro hS3
      -- 3.4.1. def:union u := t, Y := B, Z := C, from S3
      have s3_4_1 : t ∈ B ∨ t ∈ C := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp hS3
      -- 3.4.2. mun:disjunctive-syllogism-left P := t ∈ B, Q := t ∈ C, from 3.2, 3.4.1
      have s3_4_2 : t ∈ C := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ B) (Q := t ∈ C) s3_4_1 s3_2b)
      exact s3_3 s3_4_2
    -- 3.5. def:difference u := t, Y := A, Z := B ∪ C, from 3.2, 3.4
    exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B ∪ C) (u := t))).mpr (by parley_set_side)
  -- 4. def:subset, from 3
  have s4 : (A \ B) ∩ (A \ C) ⊆ A \ (B ∪ C) := ((Parley.Items.Stdlib.Sets.def_subset (X := (A \ B) ∩ (A \ C)) (Y := A \ (B ∪ C)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (B ∪ C)) (Y := (A \ B) ∩ (A \ C)) s2 s4)

end Parley.Proofs.Hammack.DifferenceOfUnion.DifferenceOfUnion
