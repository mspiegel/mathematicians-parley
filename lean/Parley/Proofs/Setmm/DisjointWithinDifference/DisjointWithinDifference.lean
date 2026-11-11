module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/disjoint-within-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DisjointWithinDifference.DisjointWithinDifference

theorem disjoint_within_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ C) :
    (A ∩ B = ∅ ↔ A ⊆ C \ B) := by
  -- the theorem. both directions
  constructor
  · skip
    intro hD1
    -- 1. proof
    have s1 : ∀ t ∈ A, t ∈ C \ B := by
      intro t hK
      -- 1.1. mun:in-subset X := A, Y := C, u := t, from H4, K
      have s1_1 : t ∈ C := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := C) (u := t) hH4 hK)
      -- 1.2. mun:disjoint-member Y := A, Z := B, u := t, from D1, K
      have s1_2 : ¬ t ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A) (Z := B) (u := t) hD1 hK)
      -- 1.3. def:difference u := t, Y := C, Z := B, from 1.1, 1.2
      exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := t))).mpr ⟨s1_1, s1_2⟩
    -- 2. def:subset X := A, Y := C ∖ B, from 1
    exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mpr s1
  · skip
    intro hD2
    -- 3. def:subset X := A, Y := C ∖ B, from D2
    have s3 : ∀ t ∈ A, t ∈ C \ B := by exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := C \ B))).mp hD2
    -- 4. proof
    have s4 : ∀ s ∈ A, ¬ s ∈ B := by
      intro s hK
      -- 4.1. instantiate t := s in line 3, from K
      have s4_1 : s ∈ C \ B := by exact (s3 s hK)
      -- 4.2. def:difference u := s, Y := C, Z := B, from 4.1
      have s4_2 : s ∈ C ∧ ¬ s ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_difference (Y := C) (Z := B) (u := s))).mp s4_1
      -- 4.3. restate 4.2
      exact s4_2.2
    -- 5. calculation
    calc A ∩ B = B ∩ A := by exact (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := A) (Z := B))
      _ = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_empty (Y := B) (Z := A) s4)

end Parley.Proofs.Setmm.DisjointWithinDifference.DisjointWithinDifference
