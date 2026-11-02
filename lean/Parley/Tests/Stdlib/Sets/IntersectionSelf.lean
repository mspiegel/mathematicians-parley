module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionSelf

theorem intersection_self {α : Type*} (Y : Set α) :
    Y ∩ Y = Y := by
  -- 1. mun:sets-intersection-self
  have s1 : Y ∩ Y = Y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Sets.IntersectionSelf
