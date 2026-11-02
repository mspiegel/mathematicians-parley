module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.UnionDifference

theorem union_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z \ Y = Y ∪ Z := by
  -- 1. mun:sets-union-difference
  have s1 : Y ∪ Z \ Y = Y ∪ Z := by first | exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z)) | exact ((Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z)) | (have h := (Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Sets.UnionDifference
