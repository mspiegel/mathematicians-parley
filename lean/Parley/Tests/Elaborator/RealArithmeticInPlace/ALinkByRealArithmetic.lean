module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic

theorem a_link_by_real_arithmetic :
    Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 3 * Real.sqrt (2 : ℝ) := by
  -- 1. calculation
  have s1 : Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 3 * Real.sqrt (2 : ℝ) := by
    calc Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 2 * Real.sqrt (2 : ℝ) + Real.sqrt (2 : ℝ) := by parley_real
      _ = 3 * Real.sqrt (2 : ℝ) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic
