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

namespace Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight

theorem intersection_subset_right {α : Type*} (A : Set α) (B : Set α) :
    A ∩ B ⊆ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A ∩ B, u ∈ B := by
    intro u hK1
    -- 1.1. def:intersection, from K1
    have s1_1 : u ∈ A ∧ u ∈ B := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp hK1
    -- 1.2. restate 1.1
    parley_set_side
  -- 2. def:subset, from 1
  first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := B))).mpr s1 | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := B))).mpr s1; parley_set_side)

end Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight
