module

public import RealTactics
public import Tactics

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfAWholeNumberAndALogarithm

theorem an_exponential_of_a_whole_number_and_a_logarithm :
    Real.exp (2 + Real.log (3 : ℝ)) = 3 * Real.exp 1 ^ 2 := by
  -- 1. real arithmetic
  have s1 : Real.exp (2 + Real.log (3 : ℝ)) = 3 * Real.exp 1 ^ 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfAWholeNumberAndALogarithm
