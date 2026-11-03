module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.APowerWithHalvedCoefficients

theorem a_power_with_halved_coefficients :
    ((1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) / 2) ^ 6 = 81 / 4 + 55 / 4 * Real.sqrt (2 : ℝ) + 45 / 4 * Real.sqrt (3 : ℝ) + 33 / 4 * Real.sqrt (6 : ℝ) := by
  -- 1. real arithmetic
  have s1 : ((1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ)) / 2) ^ 6 = 81 / 4 + 55 / 4 * Real.sqrt (2 : ℝ) + 45 / 4 * Real.sqrt (3 : ℝ) + 33 / 4 * Real.sqrt (6 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.APowerWithHalvedCoefficients
