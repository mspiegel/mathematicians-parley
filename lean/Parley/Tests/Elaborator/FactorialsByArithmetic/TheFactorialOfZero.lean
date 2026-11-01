module

public import Parley.Library

/-! Written from tests/elaborator/factorials-by-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FactorialsByArithmetic.TheFactorialOfZero

theorem the_factorial_of_zero :
    (Nat.factorial 0 : ℤ) = 1 := by
  -- 1. arithmetic
  have s1 : (Nat.factorial 0 : ℤ) = 1 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.FactorialsByArithmetic.TheFactorialOfZero
