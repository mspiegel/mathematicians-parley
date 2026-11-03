module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfAHalf

theorem a_root_of_a_half :
    2 * Real.sqrt (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : 2 * Real.sqrt (1 / 2 : ℝ) = Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootOfAHalf
