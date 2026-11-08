module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeBelowMinusOne

theorem minus_three_below_minus_one :
    (-3 : ℤ) ≤ -1 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusThreeBelowMinusOne
