module

public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-union-right.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight

theorem subset_of_union_right {α : Type*} (A : Set α) (B : Set α) :
    A ⊆ B ∪ A := by
  -- 1. proof
  have s1 : ∀ u ∈ A, u ∈ B ∪ A := by
    intro u hK1
    -- 1.1. mun:in-union-right, from K1
    have s1_1 : u ∈ B ∪ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_side)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_side)); parley_side)
    all_goals parley_side
  -- 2. def:subset, from 1
  have s2 : A ⊆ B ∪ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight
