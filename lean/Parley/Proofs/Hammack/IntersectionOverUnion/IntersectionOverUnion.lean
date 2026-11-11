module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/intersection-over-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.IntersectionOverUnion.IntersectionOverUnion

theorem intersection_over_union {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C := by
  -- 1. proof
  have s1 : ∀ t ∈ A ∩ (B ∪ C), t ∈ A ∩ B ∪ A ∩ C := by
    intro t hK1
    -- 1.1. def:intersection u := t, Y := A, Z := B ∪ C, from K1
    have s1_1a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B ∪ C) (u := t))).mp hK1).1
    have s1_1b : t ∈ B ∪ C := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B ∪ C) (u := t))).mp hK1).2
    -- 1.2. def:union u := t, Y := B, Z := C, from 1.1
    have s1_2 : t ∈ B ∨ t ∈ C := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := B) (Z := C) (u := t))).mp s1_1b
    -- 1.3. cases, from 1.2
    rcases s1_2 with hC1 | hC2
    · skip
      -- 1.3.1. def:intersection u := t, Y := A, Z := B, from C1, 1.1
      have s1_3_1 : t ∈ A ∩ B := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr ⟨s1_1a, hC1⟩
      -- 1.3.2. mun:in-union-left u := t, Y := A ∩ B, Z := A ∩ C, from 1.3.1
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A ∩ B) (Z := A ∩ C) (u := t) s1_3_1)
    · skip
      -- 1.3.3. def:intersection u := t, Y := A, Z := C, from C2, 1.1
      have s1_3_3 : t ∈ A ∩ C := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := t))).mpr ⟨s1_1a, hC2⟩
      -- 1.3.4. mun:in-union-right u := t, Y := A ∩ B, Z := A ∩ C, from 1.3.3
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A ∩ B) (Z := A ∩ C) (u := t) s1_3_3)
  -- 2. def:subset, from 1
  have s2 : A ∩ (B ∪ C) ⊆ A ∩ B ∪ A ∩ C := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ (B ∪ C)) (Y := A ∩ B ∪ A ∩ C))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ A ∩ B ∪ A ∩ C, t ∈ A ∩ (B ∪ C) := by
    intro t hK2
    -- 3.1. def:union u := t, Y := A ∩ B, Z := A ∩ C, from K2
    have s3_1 : t ∈ A ∩ B ∨ t ∈ A ∩ C := by exact ((Parley.Items.Stdlib.Sets.def_union (Y := A ∩ B) (Z := A ∩ C) (u := t))).mp hK2
    -- 3.2. cases, from 3.1
    rcases s3_1 with hC3 | hC4
    · skip
      -- 3.2.1. def:intersection u := t, Y := A, Z := B, from C3
      have s3_2_1a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp hC3).1
      have s3_2_1b : t ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp hC3).2
      -- 3.2.2. mun:in-union-left u := t, Y := B, Z := C, from 3.2.1
      have s3_2_2 : t ∈ B ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := B) (Z := C) (u := t) s3_2_1b)
      -- 3.2.3. def:intersection u := t, Y := A, Z := B ∪ C, from 3.2.1, 3.2.2
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B ∪ C) (u := t))).mpr ⟨s3_2_1a, s3_2_2⟩
    · skip
      -- 3.2.4. def:intersection u := t, Y := A, Z := C, from C4
      have s3_2_4a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := t))).mp hC4).1
      have s3_2_4b : t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := t))).mp hC4).2
      -- 3.2.5. mun:in-union-right u := t, Y := B, Z := C, from 3.2.4
      have s3_2_5 : t ∈ B ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := C) (u := t) s3_2_4b)
      -- 3.2.6. def:intersection u := t, Y := A, Z := B ∪ C, from 3.2.4, 3.2.5
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B ∪ C) (u := t))).mpr ⟨s3_2_4a, s3_2_5⟩
  -- 4. def:subset, from 3
  have s4 : A ∩ B ∪ A ∩ C ⊆ A ∩ (B ∪ C) := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B ∪ A ∩ C) (Y := A ∩ (B ∪ C)))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∩ (B ∪ C)) (Y := A ∩ B ∪ A ∩ C) s2 s4)

end Parley.Proofs.Hammack.IntersectionOverUnion.IntersectionOverUnion
