module

public import ArithTactics
public import Tactics
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-negative-power-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerByArithmetic

theorem a_negative_power_by_arithmetic :
    (2 ^ (-1 : ℤ) : ℚ) < 1 := by
  -- 1. arithmetic
  have s1 : (2 ^ (-1 : ℤ) : ℚ) < 1 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerByArithmetic
