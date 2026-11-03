module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfALogarithm

theorem an_exponential_of_a_logarithm :
    Real.exp (Real.log (5 : ℝ)) = 5 := by
  -- 1. real arithmetic
  have s1 : Real.exp (Real.log (5 : ℝ)) = 5 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfALogarithm
