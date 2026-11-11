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

theorem intersection_then_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ∩ B) \ C = (A \ C) ∩ (B \ C) := by
  -- 1. proof
  have s1 : ∀ t ∈ (A ∩ B) \ C, t ∈ (A \ C) ∩ (B \ C) := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A ∩ B, Z := C, from K1
    have s1_1a : t ∈ A ∩ B := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp hK1).1
    have s1_1b : ¬ t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mp hK1).2
    -- 1.2. def:intersection u := t, Y := A, Z := B, from 1.1
    have s1_2a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp s1_1a).1
    have s1_2b : t ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mp s1_1a).2
    -- 1.3. def:difference u := t, Y := A, Z := C, from 1.1, 1.2
    have s1_3 : t ∈ A \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mpr ⟨s1_2a, s1_1b⟩
    -- 1.4. def:difference u := t, Y := B, Z := C, from 1.1, 1.2
    have s1_4 : t ∈ B \ C := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr ⟨s1_2b, s1_1b⟩
    -- 1.5. def:intersection u := t, Y := A ∖ C, Z := B ∖ C, from 1.3, 1.4
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mpr ⟨s1_3, s1_4⟩
  -- 2. def:subset, from 1
  have s2 : (A ∩ B) \ C ⊆ (A \ C) ∩ (B \ C) := ((Parley.Items.Stdlib.Sets.def_subset (X := (A ∩ B) \ C) (Y := (A \ C) ∩ (B \ C)))).mpr s1
  -- 3. proof
  have s3 : ∀ t ∈ (A \ C) ∩ (B \ C), t ∈ (A ∩ B) \ C := by
    intro t hK2
    -- 3.1. def:intersection u := t, Y := A ∖ C, Z := B ∖ C, from K2
    have s3_1a : t ∈ A \ C := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp hK2).1
    have s3_1b : t ∈ B \ C := by exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A \ C) (Z := B \ C) (u := t))).mp hK2).2
    -- 3.2. def:difference u := t, Y := A, Z := C, from 3.1
    have s3_2a : t ∈ A := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp s3_1a).1
    have s3_2b : ¬ t ∈ C := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp s3_1a).2
    -- 3.3. def:difference u := t, Y := B, Z := C, from 3.1
    have s3_3 : t ∈ B := by exact (((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mp s3_1b).1
    -- 3.4. def:intersection u := t, Y := A, Z := B, from 3.2, 3.3
    have s3_4 : t ∈ A ∩ B := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := t))).mpr ⟨s3_2a, s3_3⟩
    -- 3.5. def:difference u := t, Y := A ∩ B, Z := C, from 3.2, 3.4
    exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A ∩ B) (Z := C) (u := t))).mpr ⟨s3_4, s3_2b⟩
  -- 4. def:subset, from 3
  have s4 : (A \ C) ∩ (B \ C) ⊆ (A ∩ B) \ C := ((Parley.Items.Stdlib.Sets.def_subset (X := (A \ C) ∩ (B \ C)) (Y := (A ∩ B) \ C))).mpr s3
  -- 5. mun:subset-antisymmetric, from 2, 4
  exact (Parley.Items.Stdlib.Sets.mun_subset_antisymmetric (X := (A ∩ B) \ C) (Y := (A \ C) ∩ (B \ C)) s2 s4)

end Parley.Proofs.Hammack.IntersectionThenDifference.IntersectionThenDifference
