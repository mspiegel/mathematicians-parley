module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/set-order-laws.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SetOrderLaws.IntersectionKeepsOrder

theorem intersection_keeps_order {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B) :
    A ∩ C ⊆ B ∩ C := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ C, u ∈ B ∩ C := by
    intro u hK1
    -- 1.1. def:intersection, from K1
    have s1_1 : u ∈ A ∧ u ∈ C := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := u))).mp hK1
    -- 1.2. mun:in-subset X := A, Y := B, from H4, 1.1
    have s1_2 : u ∈ B := by exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hH4 s1_1.1)
    -- 1.3. join 1.1, 1.2
    have s1_3 : u ∈ B ∧ u ∈ C := by parley_set_side
    -- 1.4. def:intersection, from 1.3
    exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side)
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ C) (Y := B ∩ C))).mpr s1

end Parley.Proofs.Setmm.SetOrderLaws.IntersectionKeepsOrder
