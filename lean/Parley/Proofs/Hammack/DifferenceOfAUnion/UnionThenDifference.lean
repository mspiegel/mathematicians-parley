module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/difference-of-a-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceOfAUnion.UnionThenDifference

set_option maxHeartbeats 400000 in
theorem union_then_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ∪ B) \ C = A \ C ∪ B \ C := by
  -- 1. proof
  have s1 : ∀ t ∈ (A ∪ B) \ C, t ∈ A \ C ∪ B \ C := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A ∪ B, Z := C, from K1
    have s1_1a : t ∈ A ∪ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∪ B) (Z := C) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∪ B) (Z := C) (u := t))).mp hK1).2
    -- 1.2. def:union u := t, Y := A, Z := B, from 1.1
    have s1_2 : t ∈ A ∨ t ∈ B := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := t))).mp s1_1a
    -- 1.3. cases, from 1.2
    rcases s1_2 with hC1 | hC2
    · skip
      -- 1.3.1. def:difference u := t, Y := A, Z := C, from C1, 1.1
      have s1_3_1 : t ∈ A \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
      -- 1.3.2. mun:in-union-left u := t, Y := A ∖ C, Z := B ∖ C, from 1.3.1
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A \ C) (Z := B \ C) (u := t) s1_3_1)
    · skip
      -- 1.3.3. def:difference u := t, Y := B, Z := C, from C2, 1.1
      have s1_3_3 : t ∈ B \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
      -- 1.3.4. mun:in-union-right u := t, Y := A ∖ C, Z := B ∖ C, from 1.3.3
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A \ C) (Z := B \ C) (u := t) s1_3_3)
  -- 2. def:subset, from 1
  have s2 : (A ∪ B) \ C ⊆ A \ C ∪ B \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∪ B) \ C) (Y := A \ C ∪ B \ C))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∪ B) \ C) (Y := A \ C ∪ B \ C))).mpr s1; parley_set_side)
  -- 3. proof
  have s3 : ∀ t ∈ A \ C ∪ B \ C, t ∈ (A ∪ B) \ C := by
    intro t hK2
    -- 3.1. def:union u := t, Y := A ∖ C, Z := B ∖ C, from K2
    have s3_1 : t ∈ A \ C ∨ t ∈ B \ C := ((Parley.Items.Stdlib.Sets.def_union (Y := A \ C) (Z := B \ C) (u := t))).mp hK2
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC3 | hC4
    · skip
      -- 3.2.1. def:difference u := t, Y := A, Z := C, from C3
      have s3_2_1a : t ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hC3).1
      have s3_2_1b : ¬ t ∈ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp hC3).2
      -- 3.2.2. mun:in-union-left u := t, Y := A, Z := B, from 3.2.1
      have s3_2_2 : t ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := t) s3_2_1a)
      -- 3.2.3. def:difference u := t, Y := A ∪ B, Z := C, from 3.2.1, 3.2.2
      first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∪ B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∪ B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
    · skip
      -- 3.2.4. def:difference u := t, Y := B, Z := C, from C4
      have s3_2_4a : t ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp hC4).1
      have s3_2_4b : ¬ t ∈ C := (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp hC4).2
      -- 3.2.5. mun:in-union-right u := t, Y := A, Z := B, from 3.2.4
      have s3_2_5 : t ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := t) s3_2_4a)
      -- 3.2.6. def:difference u := t, Y := A ∪ B, Z := C, from 3.2.4, 3.2.5
      first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∪ B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∪ B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
  -- 4. def:subset, from 3
  have s4 : A \ C ∪ B \ C ⊆ (A ∪ B) \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ C ∪ B \ C) (Y := (A ∪ B) \ C))).mpr s3 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ C ∪ B \ C) (Y := (A ∪ B) \ C))).mpr s3; parley_set_side)
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (A ∪ B) \ C) (Y := A \ C ∪ B \ C) s2 s4)

end Parley.Proofs.Hammack.DifferenceOfAUnion.UnionThenDifference
