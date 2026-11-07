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

namespace Parley.Tests.Stdlib.Sets.UnionCommutes

theorem union_commutes {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z = Z ∪ Y := by
  -- 1. mun:sets-union-commutes
  have s1 : Y ∪ Z = Z ∪ Y := by exact (Parley.Items.Stdlib.Sets.mun_union_commutes (Y := Y) (Z := Z))
  all_goals exact s1

end Parley.Tests.Stdlib.Sets.UnionCommutes
