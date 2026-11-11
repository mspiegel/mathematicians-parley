module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-intersection-2.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfIntersection2.SubsetOfIntersection

theorem subset_of_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ u ∈ A, u ∈ B ∩ C := by
      intro u hK1
      -- 1.1. mun:in-subset X := A, Y := B, from D1, K1
      have s1_1 : u ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hD1.1 hK1)
      -- 1.2. mun:in-subset X := A, Y := C, from D1, K1
      have s1_2 : u ∈ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := u) hD1.2 hK1)
      -- 1.3. join 1.1, 1.2
      have s1_3 : u ∈ B ∧ u ∈ C := by parley_set_side
      -- 1.4. def:intersection, from 1.3
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr ⟨s1_3.1, s1_3.2⟩
    -- 2. def:subset, from 1
    exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mpr s1
  · skip
    intro hD2
    -- 3. proof
    have s3 : ∀ u ∈ A, u ∈ B ∧ u ∈ C := by
      intro u hK2
      -- 3.1. mun:in-subset X := A, Y := B ∩ C, from D2, K2
      have s3_1 : u ∈ B ∩ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B ∩ C) (u := u) hD2 hK2)
      -- 3.2. def:intersection, from 3.1
      have s3_2 : u ∈ B ∧ u ∈ C := by exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mp s3_1
      exact ⟨(s3_2).1, (s3_2).2⟩
    -- 4. proof
    have s4 : ∀ u ∈ A, u ∈ B := by
      intro u hK3
      -- 4.1. restate 3
      exact (s3 u hK3).1
    -- 5. proof
    have s5 : ∀ u ∈ A, u ∈ C := by
      intro u hK4
      -- 5.1. restate 3
      exact (s3 u hK4).2
    -- 6. def:subset, from 4
    have s6 : A ⊆ B := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr s4
    -- 7. def:subset X := A, Y := C, from 5
    have s7 : A ⊆ C := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr s5
    -- 8. join 6, 7
    have s8 : A ⊆ B ∧ A ⊆ C := by parley_set_side
    exact ⟨(s8).1, (s8).2⟩

end Parley.Proofs.Setmm.SubsetOfIntersection2.SubsetOfIntersection
