module

public import Parley.Library

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits

theorem a_factorial_of_several_digits :
    (Parley.Library.factorial (12 : ℤ) : ℤ) = 479001600 := by
  -- 1. arithmetic
  have s1 : (Parley.Library.factorial (12 : ℤ) : ℤ) = 479001600 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits
