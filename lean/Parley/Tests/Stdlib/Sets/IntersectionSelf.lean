module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionSelf

theorem intersection_self {α : Type*} (Y : Set α) :
    Y ∩ Y = Y := by
  -- 1. mun:sets-intersection-self
  have s1 : Y ∩ Y = Y := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); simp only [Set.pair_comm, Set.insert_comm] at h ⊢; exact h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Sets.IntersectionSelf
