module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionCommutes

theorem intersection_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∩ Z = Z ∩ Y := by
  -- 1. mun:sets-intersection-commutes
  have s1 : Y ∩ Z = Z ∩ Y := by first | exact (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)) | exact ((Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z))).symm | simpa using (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)) | exact_mod_cast (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)) | (have h := (Parley.Items.Stdlib.Sets.mun_intersection_commutes (Y := Y) (Z := Z)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.IntersectionCommutes
