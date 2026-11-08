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

namespace Parley.Tests.Stdlib.Sets.DifferenceSelf

theorem difference_self {α : Type*} (Y : Set α) :
    Y \ Y = ∅ := by
  -- 1. mun:sets-difference-self
  exact (Parley.Items.Stdlib.Sets.mun_difference_self (Y := Y))

end Parley.Tests.Stdlib.Sets.DifferenceSelf
