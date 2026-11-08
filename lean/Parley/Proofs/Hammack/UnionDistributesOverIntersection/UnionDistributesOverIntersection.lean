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

/-! Written from proofs/hammack/union-distributes-over-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.UnionDistributesOverIntersection.UnionDistributesOverIntersection

set_option maxHeartbeats 600000 in
theorem union_distributes_over_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) := by
  -- 1. proof
  have s1 : ∀ t ∈ A ∪ B ∩ C, t ∈ (A ∪ B) ∩ (A ∪ C) := by
    intro t hK1
    -- 1.1. def:union u := t, Y := A, Z := B ∩ C, from K1
    have s1_1 : t ∈ A ∨ t ∈ B ∩ C := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B ∩ C) (u := t))).mp hK1
    -- 1.2. cases, from 1.1
    rcases s1_1 with hC1 | hC2
    · skip
      -- 1.2.1. mun:in-union-left u := t, Y := A, Z := B, from C1
      have s1_2_1 : t ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := t) hC1)
      -- 1.2.2. mun:in-union-left u := t, Y := A, Z := C, from C1
      have s1_2_2 : t ∈ A ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := C) (u := t) hC1)
      -- 1.2.3. def:intersection u := t, Y := A ∪ B, Z := A ∪ C, from 1.2.1, 1.2.2
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := t))).mpr (by parley_set_side)
    · skip
      -- 1.2.4. def:intersection u := t, Y := B, Z := C, from C2
      have s1_2_4a : t ∈ B := (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp hC2).1
      have s1_2_4b : t ∈ C := (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp hC2).2
      -- 1.2.5. mun:in-union-right u := t, Y := A, Z := B, from 1.2.4
      have s1_2_5 : t ∈ A ∪ B := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B) (u := t) s1_2_4a)
      -- 1.2.6. mun:in-union-right u := t, Y := A, Z := C, from 1.2.4
      have s1_2_6 : t ∈ A ∪ C := by exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := C) (u := t) s1_2_4b)
      -- 1.2.7. def:intersection u := t, Y := A ∪ B, Z := A ∪ C, from 1.2.5, 1.2.6
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := t))).mpr (by parley_set_side)
  -- 2. def:subset, from 1
  have s2 : A ∪ B ∩ C ⊆ (A ∪ B) ∩ (A ∪ C) := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∪ B ∩ C) (Y := (A ∪ B) ∩ (A ∪ C)))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ (A ∪ B) ∩ (A ∪ C), t ∈ A ∪ B ∩ C := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := A ∪ B, Z := A ∪ C, from K2
    have s3_1a : t ∈ A ∪ B := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := t))).mp hK2).1
    have s3_1b : t ∈ A ∪ C := (((Parley.Items.Stdlib.Sets.def_intersection (Y := A ∪ B) (Z := A ∪ C) (u := t))).mp hK2).2
    -- 3.2. def:union u := t, Y := A, Z := B, from 3.1
    have s3_2 : t ∈ A ∨ t ∈ B := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := B) (u := t))).mp s3_1a
    -- 3.3. def:union u := t, Y := A, Z := C, from 3.1
    have s3_3 : t ∈ A ∨ t ∈ C := ((Parley.Items.Stdlib.Sets.def_union (Y := A) (Z := C) (u := t))).mp s3_1b
    -- 3.4. axi:excluded-middle P := t ∈ A
    have s3_4 : t ∈ A ∨ ¬ t ∈ A := by exact (Parley.Items.Stdlib.Reasoning.axi_excluded_middle (P := t ∈ A))
    -- 3.5. cases, from 3.4
    rcases s3_4 with hC3 | hC4
    · skip
      -- 3.5.1. mun:in-union-left u := t, Y := A, Z := B ∩ C, from C3
      exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B ∩ C) (u := t) hC3)
    · skip
      -- 3.5.2. mun:disjunctive-syllogism-left, from C4, 3.2
      have s3_5_2 : t ∈ B := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ A) (Q := t ∈ B) s3_2 hC4)
      -- 3.5.3. mun:disjunctive-syllogism-left, from C4, 3.3
      have s3_5_3 : t ∈ C := by exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := t ∈ A) (Q := t ∈ C) s3_3 hC4)
      -- 3.5.4. def:intersection u := t, Y := B, Z := C, from 3.5.2, 3.5.3
      have s3_5_4 : t ∈ B ∩ C := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr (by parley_set_side)
      -- 3.5.5. mun:in-union-right u := t, Y := A, Z := B ∩ C, from 3.5.4
      exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := A) (Z := B ∩ C) (u := t) s3_5_4)
  -- 4. def:subset, from 3
  have s4 : (A ∪ B) ∩ (A ∪ C) ⊆ A ∪ B ∩ C := ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∪ B) ∩ (A ∪ C)) (Y := A ∪ B ∩ C))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := A ∪ B ∩ C) (Y := (A ∪ B) ∩ (A ∪ C)) s2 s4)

end Parley.Proofs.Hammack.UnionDistributesOverIntersection.UnionDistributesOverIntersection
