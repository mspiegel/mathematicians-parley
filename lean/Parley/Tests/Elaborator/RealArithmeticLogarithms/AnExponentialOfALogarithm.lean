module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfALogarithm

theorem an_exponential_of_a_logarithm :
    Real.exp (Real.log (5 : ℝ)) = 5 := by
  -- 1. real arithmetic
  have s1 : Real.exp (Real.log (5 : ℝ)) = 5 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfALogarithm
