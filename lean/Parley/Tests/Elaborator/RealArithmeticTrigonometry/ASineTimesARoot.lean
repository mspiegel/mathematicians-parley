module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineTimesARoot

theorem a_sine_times_a_root :
    Real.sin (Real.pi / 4) * Real.sqrt (2 : ℝ) = 1 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 4) * Real.sqrt (2 : ℝ) = 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineTimesARoot
