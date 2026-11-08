module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight

theorem at_least_one_right (x : ℤ) (hH2 : x ≥ 1) :
    0 < x := by
  -- 1. inequalities, from H2
  parley_order

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.AtLeastOneRight
