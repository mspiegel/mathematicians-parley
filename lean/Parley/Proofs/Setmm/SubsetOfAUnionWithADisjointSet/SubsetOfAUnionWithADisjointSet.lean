module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-a-union-with-a-disjoint-set.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfAUnionWithADisjointSet.SubsetOfAUnionWithADisjointSet

set_option maxHeartbeats 400000 in
theorem subset_of_a_union_with_a_disjoint_set {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ∩ B = ∅) :
    (A ⊆ B ∪ C ↔ A ⊆ C) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ t ∈ A, t ∈ C := by
      intro t hK1
      -- 1.1. mun:disjoint-member Y := A, Z := B, from H4, K1
      have s1_1 : ¬ t ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hH4 hK1)
      -- 1.2. mun:in-subset X := A, Y := B ∪ C, u := t, from D1, K1
      have s1_2 : t ∈ B ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∪ C) (u := t) hD1 hK1)
      -- 1.3. def:union u := t, Y := B, Z := C, from 1.2
      have s1_3 : t ∈ B ∨ t ∈ C := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp s1_2
      -- 1.4. cases, from 1.3
      rcases s1_3 with hC1 | hC2
      · skip
        -- 1.4.1. restate C1
        have s1_4_1 : t ∈ B := by parley_set_side
        exact absurd s1_4_1 s1_1
      · skip
        exact hC2
    -- 2. def:subset, from 1
    exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr s1
  · skip
    intro hD2
    -- 3. proof
    have s3 : ∀ t ∈ A, t ∈ B ∪ C := by
      intro t hK2
      -- 3.1. mun:in-subset X := A, Y := C, u := t, from D2, K2
      have s3_1 : t ∈ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hD2 hK2)
      -- 3.2. mun:in-union-right Y := B, Z := C, from 3.1
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) s3_1)
    -- 4. def:subset, from 3
    exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ C))).mpr s3

end Parley.Proofs.Setmm.SubsetOfAUnionWithADisjointSet.SubsetOfAUnionWithADisjointSet
