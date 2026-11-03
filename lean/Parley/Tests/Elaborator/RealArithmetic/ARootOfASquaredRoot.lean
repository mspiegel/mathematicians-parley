module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfASquaredRoot

theorem a_root_of_a_squared_root :
    Real.sqrt (Real.sqrt (2 : ℝ) ^ 2) = Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (Real.sqrt (2 : ℝ) ^ 2) = Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmetic.ARootOfASquaredRoot
