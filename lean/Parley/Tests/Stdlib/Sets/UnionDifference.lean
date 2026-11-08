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

namespace Parley.Tests.Stdlib.Sets.UnionDifference

theorem union_difference {α : Type*} (Y : Set α) (Z : Set α) :
    Y ∪ Z \ Y = Y ∪ Z := by
  -- 1. mun:sets-union-difference
  exact (Parley.Items.Stdlib.Sets.mun_union_difference (Y := Y) (Z := Z))

end Parley.Tests.Stdlib.Sets.UnionDifference
