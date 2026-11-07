module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/intersection-then-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.IntersectionThenDifference.IntersectionThenDifference

set_option maxHeartbeats 400000 in
theorem intersection_then_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ∩ B) \ C = (A \ C) ∩ (B \ C) := by
  -- 1. proof
  have s1 : ∀ t ∈ (A ∩ B) \ C, t ∈ (A \ C) ∩ (B \ C) := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A ∩ B, Z := C, from K1
    have s1_1a : t ∈ A ∩ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s1_1b : ¬ t ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. def:intersection u := t, Y := A, Z := B, from 1.1
    have s1_2a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s1_2b : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.3. def:difference u := t, Y := A, Z := C, from 1.1, 1.2
    have s1_3 : t ∈ A \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
    -- 1.4. def:difference u := t, Y := B, Z := C, from 1.1, 1.2
    have s1_4 : t ∈ B \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
    -- 1.5. def:intersection u := t, Y := A ∖ C, Z := B ∖ C, from 1.3, 1.4
    have s1_5 : t ∈ (A \ C) ∩ (B \ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_5
  -- 2. def:subset, from 1
  have s2 : (A ∩ B) \ C ⊆ (A \ C) ∩ (B \ C) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∩ B) \ C) (Y := (A \ C) ∩ (B \ C)))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∩ B) \ C) (Y := (A \ C) ∩ (B \ C)))).mpr (by parley_set_side); parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ (A \ C) ∩ (B \ C), t ∈ (A ∩ B) \ C := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := A ∖ C, Z := B ∖ C, from K2
    have s3_1a : t ∈ A \ C := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s3_1b : t ∈ B \ C := by first | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 3.2. def:difference u := t, Y := A, Z := C, from 3.1
    have s3_2a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s3_2b : ¬ t ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 3.3. def:difference u := t, Y := B, Z := C, from 3.1
    have s3_3 : t ∈ B := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    -- 3.4. def:intersection u := t, Y := A, Z := B, from 3.2, 3.3
    have s3_4 : t ∈ A ∩ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
    -- 3.5. def:difference u := t, Y := A ∩ B, Z := C, from 3.2, 3.4
    have s3_5 : t ∈ (A ∩ B) \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s3_5
  -- 4. def:subset, from 3
  have s4 : (A \ C) ∩ (B \ C) ⊆ (A ∩ B) \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (A \ C) ∩ (B \ C)) (Y := (A ∩ B) \ C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (A \ C) ∩ (B \ C)) (Y := (A ∩ B) \ C))).mpr (by parley_set_side); parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  have s5 : (A ∩ B) \ C = (A \ C) ∩ (B \ C) := by exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (A ∩ B) \ C) (Y := (A \ C) ∩ (B \ C)) s2 s4)
  all_goals exact s5

end Parley.Proofs.Hammack.IntersectionThenDifference.IntersectionThenDifference
