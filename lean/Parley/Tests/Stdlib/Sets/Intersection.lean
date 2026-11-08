module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.Intersection

theorem intersection {α : Type*} (Y : Set α) (Z : Set α) (u : α) (hH4 : u ∈ Y ∩ Z) :
    (u ∈ Y ∧ u ∈ Z) := by
  -- 1. def:sets-intersection, from H4
  exact ((Parley.Items.Stdlib.Sets.def_intersection (Y := Y) (Z := Z) (u := u))).mp hH4

end Parley.Tests.Stdlib.Sets.Intersection
