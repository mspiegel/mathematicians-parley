module

public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineSaidOnce

theorem a_sine_said_once (a : ℝ) :
    a * Real.sin (Real.pi / 6) = Real.sin (Real.pi / 6) * a := by
  -- 1. algebra
  have s1 : a * Real.sin (Real.pi / 6) = Real.sin (Real.pi / 6) * a := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineSaidOnce
