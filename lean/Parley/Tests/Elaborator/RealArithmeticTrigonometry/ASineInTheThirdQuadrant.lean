module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineInTheThirdQuadrant

theorem a_sine_in_the_third_quadrant :
    Real.sin (7 * Real.pi / 6) = -(1 / 2) := by
  -- 1. real arithmetic
  have s1 : Real.sin (7 * Real.pi / 6) = -(1 / 2) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineInTheThirdQuadrant
