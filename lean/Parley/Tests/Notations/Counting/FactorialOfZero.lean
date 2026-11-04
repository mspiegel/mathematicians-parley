module

public import ArithTactics
public import Counting
public import Tactics

/-! Written from tests/notations/counting.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Counting.FactorialOfZero

theorem factorial_of_zero :
    (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 := by
  -- 1. arithmetic
  have s1 : (LeanBridges.Counting.factorial (0 : ℤ) : ℤ) = 1 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Counting.FactorialOfZero
