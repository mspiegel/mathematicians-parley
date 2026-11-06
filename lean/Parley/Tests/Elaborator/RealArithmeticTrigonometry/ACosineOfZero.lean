module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfZero

theorem a_cosine_of_zero :
    Real.cos (0 : ℝ) = 1 := by
  -- 1. real arithmetic
  have s1 : Real.cos (0 : ℝ) = 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ACosineOfZero
