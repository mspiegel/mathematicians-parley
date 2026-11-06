module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfANegativeAngle

theorem a_cosine_of_a_negative_angle :
    Real.cos (-(Real.pi / 3)) = 1 / 2 := by
  -- 1. real arithmetic
  have s1 : Real.cos (-(Real.pi / 3)) = 1 / 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfANegativeAngle
