module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ANegativePower

theorem a_negative_power :
    (1 + Real.sqrt (2 : ℝ)) ^ (-2 : ℤ) = 3 - 2 * Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (1 + Real.sqrt (2 : ℝ)) ^ (-2 : ℤ) = 3 - 2 * Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ANegativePower
