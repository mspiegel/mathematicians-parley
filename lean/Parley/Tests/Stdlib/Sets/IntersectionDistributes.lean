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

namespace Parley.Tests.Stdlib.Sets.IntersectionDistributes

theorem intersection_distributes {α : Type*} (X : Set α) (Y : Set α) (Z : Set α) :
    X ∩ (Y ∪ Z) = X ∩ Y ∪ X ∩ Z := by
  -- 1. mun:sets-intersection-distributes
  have s1 : X ∩ (Y ∪ Z) = X ∩ Y ∪ X ∩ Z := by exact (Parley.Items.Stdlib.Sets.mun_intersection_distributes (X := X) (Y := Y) (Z := Z))
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.IntersectionDistributes
