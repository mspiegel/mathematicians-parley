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
    have s1_1 : u ∈ A ∧ u ∈ B := by exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp hK1
    -- 1.2. restate 1.1
    parley_set_side
  -- 2. def:subset, from 1
  exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr s1

end Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft
