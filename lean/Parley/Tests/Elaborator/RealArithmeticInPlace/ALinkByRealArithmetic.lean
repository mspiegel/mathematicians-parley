module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic

theorem a_link_by_real_arithmetic :
    Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 3 * Real.sqrt (2 : ℝ) := by
  -- 1. calculation
  calc Real.sqrt (8 : ℝ) + Real.sqrt (2 : ℝ) = 2 * Real.sqrt (2 : ℝ) + Real.sqrt (2 : ℝ) := by parley_real
    _ = 3 * Real.sqrt (2 : ℝ) := by parley_real

end Parley.Tests.Elaborator.RealArithmeticInPlace.ALinkByRealArithmetic
