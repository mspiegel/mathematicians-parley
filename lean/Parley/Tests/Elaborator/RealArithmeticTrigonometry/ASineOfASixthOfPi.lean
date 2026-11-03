module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineOfASixthOfPi

theorem a_sine_of_a_sixth_of_pi :
    Real.sin (Real.pi / 6) = 1 / 2 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 6) = 1 / 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineOfASixthOfPi
