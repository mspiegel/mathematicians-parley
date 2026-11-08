module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeBelowZero

theorem minus_three_below_zero :
    (-3 : ℤ) < 0 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusThreeBelowZero
