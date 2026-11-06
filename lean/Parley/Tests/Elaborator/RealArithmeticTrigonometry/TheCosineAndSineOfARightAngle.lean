module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheCosineAndSineOfARightAngle

theorem the_cosine_and_sine_of_a_right_angle :
    Real.cos (Real.pi / 2) = 0 ∧ Real.sin (Real.pi / 2) = 1 := by
  -- 1. real arithmetic
  have s1a : Real.cos (Real.pi / 2) = 0 := by parley_real
  have s1b : Real.sin (Real.pi / 2) = 1 := by parley_real
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.TheCosineAndSineOfARightAngle
