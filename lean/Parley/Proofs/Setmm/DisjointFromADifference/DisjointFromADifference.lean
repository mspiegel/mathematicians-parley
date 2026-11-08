module

public import SetTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/disjoint-from-a-difference.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DisjointFromADifference.DisjointFromADifference

theorem disjoint_from_a_difference {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : (A \ B) ∩ C = ∅) :
    (C ⊆ A → C ⊆ B) := by
  -- the theorem. proof
  intro hK1
  -- 1. proof
  have s1 : ∀ t ∈ C, t ∈ B := by
    intro t hK2
    by_contra hS
    -- 1.1. mun:in-subset X := C, Y := A, u := t, from K1, K2
    have s1_1 : t ∈ A := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := C) (Y := A) (u := t) hK1 hK2)
    -- 1.2. def:difference u := t, Y := A, Z := B, from S, 1.1
    have s1_2 : t ∈ A \ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := B) (u := t))).mpr (by parley_set_side); parley_set_side)
    -- 1.3. mun:disjoint-member Y := A ∖ B, Z := C, from H4, 1.2
    have s1_3 : ¬ t ∈ C := by exact (Parley.Items.Stdlib.Sets.mun_disjoint_member (Y := A \ B) (Z := C) (u := t) hH4 s1_2)
    exact s1_3 hK2
  -- 2. def:subset, from 1
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := B))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := C) (Y := B))).mpr s1; parley_set_side)

end Parley.Proofs.Setmm.DisjointFromADifference.DisjointFromADifference
