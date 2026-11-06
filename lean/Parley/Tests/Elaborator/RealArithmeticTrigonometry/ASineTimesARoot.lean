module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineTimesARoot

theorem a_sine_times_a_root :
    Real.sin (Real.pi / 4) * Real.sqrt (2 : ℝ) = 1 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 4) * Real.sqrt (2 : ℝ) = 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineTimesARoot
