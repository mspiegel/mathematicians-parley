module

public import SetTactics
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
    have s1_1 : u ∈ B ∪ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) hK1) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) hK1)).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) hK1) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) hK1) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) hK1); parley_set_side)
    all_goals exact s1_1
  -- 2. def:subset, from 1
  have s2 : A ⊆ B ∪ A := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A))).mpr (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_subset (X := A) (Y := B ∪ A))).mpr (by parley_set_side); parley_set_side)
  all_goals exact s2

end Parley.Proofs.Setmm.SubsetOfUnionRight.SubsetOfUnionRight
