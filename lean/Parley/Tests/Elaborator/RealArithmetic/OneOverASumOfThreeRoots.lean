module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.OneOverASumOfThreeRoots

theorem one_over_a_sum_of_three_roots :
    1 / (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ≠ 0 := by
  -- 1. real arithmetic
  have s1 : 1 / (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ≠ 0 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.OneOverASumOfThreeRoots
