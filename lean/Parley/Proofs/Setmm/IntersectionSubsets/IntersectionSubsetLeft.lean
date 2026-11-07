module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/intersection-subsets.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft

theorem intersection_subset_left {α : Type*} (A : Set α) (B : Set α) :
    A ∩ B ⊆ A := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ B, u ∈ A := by
    intro u hK1
    -- 1.1. def:intersection, from K1
    have s1_1 : u ∈ A ∧ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_set_side); parley_set_side)
    -- 1.2. restate 1.1
    have s1_2 : u ∈ A := by parley_set_side
    all_goals exact s1_2
  -- 2. def:subset, from 1
  have s2 : A ∩ B ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft
