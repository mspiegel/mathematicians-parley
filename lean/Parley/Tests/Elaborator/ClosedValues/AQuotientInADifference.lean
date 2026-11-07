module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.AQuotientInADifference

theorem a_quotient_in_a_difference :
    ((7 + 8) / 1 - 2 : ℚ) < 19 := by
  -- 1. arithmetic
  have s1 : ((7 + 8) / 1 - 2 : ℚ) < 19 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ClosedValues.AQuotientInADifference
