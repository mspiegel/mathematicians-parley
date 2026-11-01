module

public import Parley.Library

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits

theorem a_factorial_of_several_digits :
    (Nat.factorial 12 : ℤ) = 479001600 := by
  -- 1. arithmetic
  have s1 : (Nat.factorial 12 : ℤ) = 479001600 := by norm_num
  parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.AFactorialOfSeveralDigits
