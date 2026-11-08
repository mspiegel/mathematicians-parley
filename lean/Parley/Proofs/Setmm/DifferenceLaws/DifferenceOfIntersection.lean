module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceLaws.DifferenceOfIntersection

set_option maxHeartbeats 400000 in
theorem difference_of_intersection {α : Type*} (A : Set α) (B : Set α) :
    A \ (A ∩ B) = A \ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A \ (A ∩ B), u ∈ A \ B := by
    intro u hK1
    -- 1.1. def:difference, from K1
    have s1_1 : u ∈ A ∧ ¬ u ∈ A ∩ B := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := A ∩ B) (u := u))).mp hK1
    -- 1.2. contradiction
    have s1_2 : ¬ u ∈ B := by
      intro hS1
      -- 1.2.1. join S1, 1.1
      have s1_2_1 : u ∈ A ∧ u ∈ B := by parley_set_side
      -- 1.2.2. def:intersection, from 1.2.1
      have s1_2_2 : u ∈ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mpr (by parley_set_side); parley_set_side)
      exact s1_1.2 s1_2_2
    -- 1.3. join 1.1, 1.2
    have s1_3 : u ∈ A ∧ ¬ u ∈ B := by parley_set_side
    -- 1.4. def:difference, from 1.3
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side); parley_set_side)
  -- 2. def:subset, from 1
  have s2 : A \ (A ∩ B) ⊆ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (A ∩ B)) (Y := A \ B))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ (A ∩ B)) (Y := A \ B))).mpr s1; parley_set_side)
  -- 3. proof
  have s3 : ∀ u ∈ A \ B, u ∈ A \ (A ∩ B) := by
    intro u hK2
    -- 3.1. def:difference, from K2
    have s3_1 : u ∈ A ∧ ¬ u ∈ B := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp hK2
    -- 3.2. contradiction
    have s3_2 : ¬ u ∈ A ∩ B := by
      intro hS2
      -- 3.2.1. def:intersection, from S2
      have s3_2_1 : u ∈ A ∧ u ∈ B := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp hS2
      -- 3.2.2. restate 3.2.1
      have s3_2_2 : u ∈ B := by parley_set_side
      exact s3_1.2 s3_2_2
    -- 3.3. join 3.1, 3.2
    have s3_3 : u ∈ A ∧ ¬ u ∈ A ∩ B := by parley_set_side
    -- 3.4. def:difference, from 3.3
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := A ∩ B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := A ∩ B) (u := u))).mpr (by parley_set_side); parley_set_side)
  -- 4. def:subset, from 3
  have s4 : A \ B ⊆ A \ (A ∩ B) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := A \ (A ∩ B)))).mpr s3 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := A \ (A ∩ B)))).mpr s3; parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ (A ∩ B)) (Y := A \ B) s2 s4)

end Parley.Proofs.Setmm.DifferenceLaws.DifferenceOfIntersection
