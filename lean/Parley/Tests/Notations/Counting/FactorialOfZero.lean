module

public import Parley.Library

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfZero

theorem factorial_of_zero :
    (Parley.Library.factorial (0 : ℤ) : ℤ) = 1 := by
  -- 1. arithmetic
  have s1 : (Parley.Library.factorial (0 : ℤ) : ℤ) = 1 := by parley_arith
  all_goals parley_side

end Parley.Tests.Notations.Counting.FactorialOfZero
