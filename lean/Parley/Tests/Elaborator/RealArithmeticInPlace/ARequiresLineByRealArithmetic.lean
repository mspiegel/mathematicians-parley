module

public import AlgebraTactics
public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ARequiresLineByRealArithmetic

theorem a_requires_line_by_real_arithmetic (a : ℝ) :
    a * (Real.sqrt (2 : ℝ) - 1) / (Real.sqrt (2 : ℝ) - 1) = a := by
  -- 1. algebra
  have r25_1 : Real.sqrt (2 : ℝ) - 1 ≠ 0 := by parley_real
  have s1 : a * (Real.sqrt (2 : ℝ) - 1) / (Real.sqrt (2 : ℝ) - 1) = a := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticInPlace.ARequiresLineByRealArithmetic
