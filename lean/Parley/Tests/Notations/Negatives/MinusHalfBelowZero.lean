module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusHalfBelowZero

theorem minus_half_below_zero :
    (-(1 / 2) : ℚ) < 0 := by
  -- 1. arithmetic
  parley_arith

end Parley.Tests.Notations.Negatives.MinusHalfBelowZero
