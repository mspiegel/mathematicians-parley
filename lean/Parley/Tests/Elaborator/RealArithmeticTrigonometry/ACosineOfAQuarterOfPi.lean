module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfAQuarterOfPi

theorem a_cosine_of_a_quarter_of_pi :
    Real.cos (Real.pi / 4) = Real.sqrt (2 : ℝ) / 2 := by
  -- 1. real arithmetic
  have s1 : Real.cos (Real.pi / 4) = Real.sqrt (2 : ℝ) / 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfAQuarterOfPi
