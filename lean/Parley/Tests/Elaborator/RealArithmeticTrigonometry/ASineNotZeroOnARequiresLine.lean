module

public import AlgebraTactics
public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine

theorem a_sine_not_zero_on_a_requires_line (a : ℝ) :
    a * Real.sin (Real.pi / 3) / Real.sin (Real.pi / 3) = a := by
  -- 1. algebra
  have r91_1 : Real.sin (Real.pi / 3) ≠ 0 := by parley_real
  have s1 : a * Real.sin (Real.pi / 3) / Real.sin (Real.pi / 3) = a := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine
