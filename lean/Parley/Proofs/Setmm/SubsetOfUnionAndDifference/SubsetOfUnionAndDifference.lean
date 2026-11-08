module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Reasoning
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-union-and-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfUnionAndDifference.SubsetOfUnionAndDifference

set_option maxHeartbeats 400000 in
theorem subset_of_union_and_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ⊆ B ∪ C ↔ A \ B ⊆ C) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ u ∈ A \ B, u ∈ C := by
      intro u hK1
      -- 1.1. def:difference Y := A, Z := B, from K1
      have s1_1a : u ∈ A := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp hK1).1
      have s1_1b : ¬ u ∈ B := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mp hK1).2
      -- 1.2. mun:in-subset X := A, Y := B ∪ C, from D1, 1.1
      have s1_2 : u ∈ B ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := u) hD1 s1_1a)
      -- 1.3. def:union Y := B, Z := C, from 1.2
      have s1_3 : u ∈ B ∨ u ∈ C := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mp s1_2
      -- 1.4. cases, from 1.3
      rcases s1_3 with hC1 | hC2
      · skip
        -- 1.4.1. restate 1.1
        have s1_4_1 : ¬ u ∈ B := by parley_set_side
        exact absurd hC1 s1_4_1
      · skip
        -- 1.4.2. restate C2
        parley_set_side
    -- 2. def:subset X := A ∖ B, Y := C, from 1
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := C))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ B) (Y := C))).mpr s1; parley_set_side)
  · skip
    intro hD2
    -- 3. proof
    have s3 : ∀ u ∈ A, u ∈ B ∪ C := by
      intro u hK2
      -- 3.1. axi:excluded-middle P := u ∈ B
      have s3_1 : u ∈ B ∨ ¬ u ∈ B := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := u ∈ B))
      -- 3.2. cases, from 3.1
      rcases s3_1 with hC1 | hC2
      · skip
        -- 3.2.1. mun:or-left, from C1
        have s3_2_1 : u ∈ B ∨ u ∈ C := by exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := u ∈ B) (Q := u ∈ C) hC1)
        -- 3.2.2. def:union Y := B, Z := C, from 3.2.1
        first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr s3_2_1 | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr s3_2_1; parley_set_side)
      · skip
        -- 3.2.3. def:difference Y := A, Z := B, from C2, K2
        have s3_2_3 : u ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := u))).mpr (by parley_set_side); parley_set_side)
        -- 3.2.4. mun:in-subset X := A ∖ B, Y := C, from D2, 3.2.3
        have s3_2_4 : u ∈ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A \ B) (Y := C) (u := u) hD2 s3_2_3)
        -- 3.2.5. mun:or-right, from 3.2.4
        have s3_2_5 : u ∈ B ∨ u ∈ C := by exact (Parley.Items.Stdlib.Reasoning.mun_or_right (P := u ∈ B) (Q := u ∈ C) s3_2_4)
        -- 3.2.6. def:union Y := B, Z := C, from 3.2.5
        first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr s3_2_5 | (have h := ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := u))).mpr s3_2_5; parley_set_side)
    -- 4. def:subset X := A, Y := B ∪ C, from 3
    first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr s3 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr s3; parley_set_side)

end Parley.Proofs.Setmm.SubsetOfUnionAndDifference.SubsetOfUnionAndDifference
