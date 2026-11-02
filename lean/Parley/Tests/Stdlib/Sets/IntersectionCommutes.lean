module

public import LeanBridges
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionCommutes

theorem intersection_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z = Z ∩ Y := by
  -- 1. mun:sets-intersection-commutes
  have s1 : Y ∩ Z = Z ∩ Y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)) | exact_mod_cast ((Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z))).symm | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Sets.IntersectionCommutes
