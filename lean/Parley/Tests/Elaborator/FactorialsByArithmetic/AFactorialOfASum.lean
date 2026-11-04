module

public import ArithTactics
public import Counting
public import Tactics

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfASum

theorem a_factorial_of_a_sum :
    (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 2 := by
  -- 1. arithmetic
  have s1 : (LeanBridges.Counting.factorial (1 + 1 : ℤ) : ℤ) = 2 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfASum
