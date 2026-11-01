module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AFourthPowerOfFourRoots

theorem a_fourth_power_of_four_roots :
    (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ) + Real.sqrt (7 : ℝ)) ^ 4 = 693 + 164 * Real.sqrt (6 : ℝ) + 148 * Real.sqrt (10 : ℝ) + 132 * Real.sqrt (14 : ℝ) + 140 * Real.sqrt (15 : ℝ) + 124 * Real.sqrt (21 : ℝ) + 108 * Real.sqrt (35 : ℝ) + 24 * Real.sqrt (210 : ℝ) := by
  -- 1. real arithmetic
  have s1 : (Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ) + Real.sqrt (7 : ℝ)) ^ 4 = 693 + 164 * Real.sqrt (6 : ℝ) + 148 * Real.sqrt (10 : ℝ) + 132 * Real.sqrt (14 : ℝ) + 140 * Real.sqrt (15 : ℝ) + 124 * Real.sqrt (21 : ℝ) + 108 * Real.sqrt (35 : ℝ) + 24 * Real.sqrt (210 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmetic.AFourthPowerOfFourRoots
