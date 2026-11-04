module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.RemainderOfASmallNumber

theorem remainder_of_a_small_number :
    (4 : ℤ) % (7 : ℤ) = 4 := by
  -- 1. arithmetic
  have s1 : (4 : ℤ) % (7 : ℤ) = 4 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.RemainderOfASmallNumber
