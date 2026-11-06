module

public import ArithTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init

/-! Written from tests/elaborator/a-negative-power-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerOfANegative

theorem a_negative_power_of_a_negative :
    ((-2) ^ (-3 : ℤ) : ℚ) = -(1 / 8) := by
  -- 1. arithmetic
  have s1 : ((-2) ^ (-3 : ℤ) : ℚ) = -(1 / 8) := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerOfANegative
