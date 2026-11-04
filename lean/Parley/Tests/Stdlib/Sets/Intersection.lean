module

public import SetTactics
public import Tactics
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Intersection

theorem intersection {α : Type*} (Y : Set α) (Z : Set α) (u : α) (hH4 : u ∈ Y ∩ Z) :
    (u ∈ Y ∧ u ∈ Z) := by
  -- 1. def:sets-intersection, from H4
  have s1 : u ∈ Y ∧ u ∈ Z := by first | exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := u))).mp (by parley_set_side) | exact (((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := u))).mp (by parley_set_side)).symm | simpa using ((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := u))).mp (by parley_set_side) | exact_mod_cast ((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := u))).mp (by parley_set_side) | (have h := ((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := u))).mp (by parley_set_side); parley_set_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.Intersection
