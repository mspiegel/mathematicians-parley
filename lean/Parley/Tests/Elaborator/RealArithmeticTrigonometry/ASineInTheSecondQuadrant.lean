module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineInTheSecondQuadrant

theorem a_sine_in_the_second_quadrant :
    Real.sin (2 * Real.pi / 3) = Real.sqrt (3 : ℝ) / 2 := by
  -- 1. real arithmetic
  have s1 : Real.sin (2 * Real.pi / 3) = Real.sqrt (3 : ℝ) / 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineInTheSecondQuadrant
