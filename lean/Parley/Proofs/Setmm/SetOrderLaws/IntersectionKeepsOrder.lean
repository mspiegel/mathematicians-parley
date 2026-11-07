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
    have s1_1 : u ∈ A ∧ u ∈ C := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := C) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 1.2. mun:in-subset X := A, Y := B, from H4, 1.1
    have s1_2 : u ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hH4 s1_1.1) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hH4 s1_1.1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hH4 s1_1.1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hH4 s1_1.1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := u) hH4 s1_1.1); parley_set_side)
    -- 1.3. join 1.1, 1.2
    have s1_3 : u ∈ B ∧ u ∈ C := by parley_set_side
    -- 1.4. def:intersection, from 1.3
    have s1_4 : u ∈ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := B) (Z := C) (u := u))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_4
  -- 2. def:subset, from 1
  have s2 : A ∩ C ⊆ B ∩ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ C) (Y := B ∩ C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ C) (Y := B ∩ C))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.SetOrderLaws.IntersectionKeepsOrder
