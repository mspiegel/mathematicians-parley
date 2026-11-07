module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/hammack/difference-keeps-subset.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.DifferenceKeepsSubset.SubsetMinusASet

theorem subset_minus_a_set {α : Type*} (A : Set α) (B : Set α) (C : Set α) (hH4 : A ⊆ B) :
    A \ C ⊆ B \ C := by
  -- 1. proof
  have s1 : ∀ t ∈ A \ C, t ∈ B \ C := by
    intro t hK1
    -- 1.1. def:difference u := t, Y := A, Z := C, from K1
    have s1_1a : t ∈ A := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).1; parley_set_side)
    have s1_1b : ¬ t ∈ C := by first | exact (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact ((((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2).symm | simpa using (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2 | exact_mod_cast (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2 | (have h := (((Parley.Items.Stdlib.Sets.def_difference (Y := A) (Z := C) (u := t))).mp (by parley_set_side)).2; parley_set_side)
    -- 1.2. mun:in-subset X := A, Y := B, u := t, from H4, 1.1
    have s1_2 : t ∈ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hH4 s1_1a) | exact ((Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hH4 s1_1a)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hH4 s1_1a) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hH4 s1_1a) | (have h := (Parley.Items.Stdlib.Sets.mun_in_subset (X := A) (Y := B) (u := t) hH4 s1_1a); parley_set_side)
    -- 1.3. def:difference u := t, Y := B, Z := C, from 1.1, 1.2
    have s1_3 : t ∈ B \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_difference (Y := B) (Z := C) (u := t))).mpr (by parley_set_side); parley_set_side)
    all_goals exact s1_3
  -- 2. def:subset, from 1
  have s2 : A \ C ⊆ B \ C := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A \ C) (Y := B \ C))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A \ C) (Y := B \ C))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Hammack.DifferenceKeepsSubset.SubsetMinusASet
