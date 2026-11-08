module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.ZeroNotBelowMinusOne

theorem zero_not_below_minus_one :
    ¬ (0 : ℤ) < -1 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.ZeroNotBelowMinusOne
