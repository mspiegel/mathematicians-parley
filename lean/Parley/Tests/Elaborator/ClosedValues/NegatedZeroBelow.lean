module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.NegatedZeroBelow

theorem negated_zero_below :
    (-0 : ℤ) ≤ 64 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Elaborator.ClosedValues.NegatedZeroBelow
