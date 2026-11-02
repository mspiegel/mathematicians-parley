module

public import Tactics
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
    have s1_1 : u ∈ A ∧ u ∈ B := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := A) (Z := B) (u := u))).mp (by parley_side); parley_side)
    -- 1.2. restate 1.1
    have s1_2 : u ∈ B := by parley_side
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : A ∩ B ⊆ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := B))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A ∩ B) (Y := B))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.IntersectionSubsets.IntersectionSubsetRight
