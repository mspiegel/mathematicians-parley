module

public import SetTactics
public import Tactics
public import Mathlib.Data.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.TypeStar
public import Parley.Items.Stdlib.Sets

/-! Written from tests/stdlib/sets.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sets.IntersectionSelf

theorem intersection_self {α : Type*} (Y : Set α) :
    Y ∩ Y = Y := by
  -- 1. mun:sets-intersection-self
  have s1 : Y ∩ Y = Y := by exact (Parley.Items.Stdlib.Sets.mun_intersection_self (Y := Y))
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.IntersectionSelf
