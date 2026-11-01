module

public import Parley.Library

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfASum

theorem a_factorial_of_a_sum :
    (Nat.factorial (1 + 1) : ℤ) = 2 := by
  -- 1. arithmetic
  have s1 : (Nat.factorial (1 + 1) : ℤ) = 2 := by norm_num
  parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfASum
