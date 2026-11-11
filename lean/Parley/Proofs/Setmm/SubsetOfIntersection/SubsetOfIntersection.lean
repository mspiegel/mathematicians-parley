module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-intersection.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfIntersection.SubsetOfIntersection

theorem subset_of_intersection {α : Type*} (A : Set α) (B : Set α) (C : Set α) :
    (A ⊆ B ∧ A ⊆ C ↔ A ⊆ B ∩ C) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. def:subset X := A, Y := B, from D1
    have s1 : ∀ t ∈ A, t ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mp hD1.1
    -- 2. def:subset X := A, Y := C, from D1
    have s2 : ∀ t ∈ A, t ∈ C := by exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mp hD1.2
    -- 3. proof
    have s3 : ∀ t ∈ A, t ∈ B ∩ C := by
      intro t hK
      -- 3.1. def:intersection u := t, from 1, 2
      exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mpr ⟨(s1 t hK), (s2 t hK)⟩
    -- 4. def:subset X := A, Y := B ∩ C, from 3
    exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mpr s3
  · skip
    intro hD2
    -- 5. def:subset X := A, Y := B ∩ C, from D2
    have s5 : ∀ t ∈ A, t ∈ B ∩ C := by exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∩ C))).mp hD2
    -- 6. proof
    have s6 : ∀ t ∈ A, t ∈ B := by
      intro t hK
      -- 6.1. def:intersection u := t, from 5
      exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (s5 t hK)).1
    -- 7. proof
    have s7 : ∀ t ∈ A, t ∈ C := by
      intro t hK
      -- 7.1. def:intersection u := t, from 5
      exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := t))).mp (s5 t hK)).2
    -- 8. def:subset X := A, Y := B, from 6
    have s8 : A ⊆ B := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B))).mpr s6
    -- 9. def:subset X := A, Y := C, from 7
    have s9 : A ⊆ C := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C))).mpr s7
    -- 10. join 8, 9
    have s10 : A ⊆ B ∧ A ⊆ C := by parley_set_side
    exact ⟨(s10).1, (s10).2⟩

end Parley.Proofs.Setmm.SubsetOfIntersection.SubsetOfIntersection
