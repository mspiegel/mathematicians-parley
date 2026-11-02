module

public import LeanBridges
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
    have s1_1 : u ∈ A ∧ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side); parley_side)
    -- 1.2. restate 1.1
    have s1_2 : u ∈ A := by parley_side
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : A ∩ B ⊆ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := A))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetLeft
