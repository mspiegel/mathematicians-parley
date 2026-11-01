module

public import Parley.Library

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic

theorem a_link_by_real_arithmetic :
    Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 3 * Real.sqrt (2 : ℝ) := by
  -- 1. calculation
  have s1 : Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 3 * Real.sqrt (2 : ℝ) := by
    calc (Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) : ℝ) = 2 * Real.sqrt (2 : ℝ) + Real.sqrt (2 : ℝ) := by norm_num
      _ = 3 * Real.sqrt (2 : ℝ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic
