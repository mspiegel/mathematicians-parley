module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ETimesTheLogarithmOfOne

theorem e_times_the_logarithm_of_one :
    Real.exp 1 * Real.log (1 : ℝ) = 0 := by
  -- 1. real arithmetic
  have s1 : Real.exp 1 * Real.log (1 : ℝ) = 0 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ETimesTheLogarithmOfOne
