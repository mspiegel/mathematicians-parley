module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from proofs/setmm/subset-of-union.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion

theorem subset_of_union {α : Type*} (A : Set α) (B : Set α) :
    A ⊆ A ∪ B := by
  -- 1. proof
  have s1 : ∀ u ∈ A, u ∈ A ∪ B := by
    intro u hK1
    -- 1.1. mun:in-union-left, from K1
    have s1_1 : u ∈ A ∪ B := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_left (Y := A) (Z := B) (u := u) (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  -- 2. def:subset, from 1
  have s2 : A ⊆ A ∪ B := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∪ B))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := A ∪ B))).mpr (by parley_set_side); parley_set_side)
  all_goals parley_set_side

end Parley.Proofs.Setmm.SubsetOfUnion.SubsetOfUnion
