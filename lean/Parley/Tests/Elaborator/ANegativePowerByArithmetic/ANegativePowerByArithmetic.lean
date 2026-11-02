module

public import LeanBridges

/-! Written from tests/elaborator/a-negative-power-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerByArithmetic

theorem a_negative_power_by_arithmetic :
    (2 ^ (-1 : ℤ) : ℚ) < 1 := by
  -- 1. arithmetic
  have s1 : (2 ^ (-1 : ℤ) : ℚ) < 1 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.ANegativePowerByArithmetic.ANegativePowerByArithmetic
