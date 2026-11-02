module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/elaborator/a-for-all-relating-two-sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllRelatingTwoSets.AForAllRelatingTwoSets

theorem a_for_all_relating_two_sets {α : Type*} (A : Set α) (B : Set α) :
    (∀ u ∈ A, u ∈ B ∪ A) := by
  -- 1. proof
  have s1 : ∀ u ∈ A, u ∈ B ∪ A := by
    intro u hK1
    -- 1.1. mun:in-union-right, from K1
    have s1_1 : u ∈ B ∪ A := by first | exact (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sets.mun_in_union_right (Y := B) (Z := A) (u := u) (by parley_set_side)); parley_set_side)
    all_goals parley_set_side
  all_goals parley_set_side

end Parley.Tests.Elaborator.AForAllRelatingTwoSets.AForAllRelatingTwoSets
