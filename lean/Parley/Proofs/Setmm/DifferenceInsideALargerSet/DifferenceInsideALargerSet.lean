module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/difference-inside-a-larger-set.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceInsideALargerSet.DifferenceInsideALargerSet

set_option maxHeartbeats 400000 in
theorem difference_inside_a_larger_set {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) :
    A \ B = (C \ B) ∩ A := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ B, t ∈ (C \ B) ∩ A := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := B, from K1
    have s1_1a : t ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mp hK1).2
    -- 1.2. mun:in-subset X := A, Y := C, u := t, from H4, 1.1
    have s1_2 : t ∈ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 s1_1a)
    -- 1.3. def:difference u := t, Y := C, Z := B, from 1.1, 1.2
    have s1_3 : t ∈ C \ B := ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr (by parley_set_side)
    -- 1.4. def:intersection u := t, Y := C ∖ B, Z := A, from 1.1, 1.3
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mpr (by parley_set_side)
  -- 2. def:subset, from 1
  have s2 : A \ B ⊆ (C \ B) ∩ A := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := (C \ B) ∩ A))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ (C \ B) ∩ A, t ∈ A \ B := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := C ∖ B, Z := A, from K2
    have s3_1a : t ∈ C \ B := (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp hK2).1
    have s3_1b : t ∈ A := (((Parley.Items.Stdlib.Sets.def_intersection (Y := C \ B) (Z := A) (u := t))).mp hK2).2
    -- 3.2. def:difference u := t, Y := C, Z := B, from 3.1
    have s3_2a : t ∈ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp s3_1a).1
    have s3_2b : ¬ t ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mp s3_1a).2
    -- 3.3. def:difference u := t, Y := A, Z := B, from 3.1, 3.2
    exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side)
  -- 4. def:subset, from 3
  have s4 : (C \ B) ∩ A ⊆ A \ B := ((Parley.Items.Stdlib.Sets.def_subset (X := (C \ B) ∩ A) (Y := A \ B))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A \ B) (Y := (C \ B) ∩ A) s2 s4)

end Parley.Proofs.Setmm.DifferenceInsideALargerSet.DifferenceInsideALargerSet
