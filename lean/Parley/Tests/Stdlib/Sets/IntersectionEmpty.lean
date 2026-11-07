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

namespace Parley.Tests.Stdlib.Sets.IntersectionEmpty

theorem intersection_empty {α : Type*} (Y : Set α) :
    Y ∩ ∅ = ∅ := by
  -- 1. mun:sets-intersection-empty
  have s1 : Y ∩ ∅ = ∅ := by exact (Parley.Items.Stdlib.Sets.mun_intersection_empty (Y := Y))
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.IntersectionEmpty
