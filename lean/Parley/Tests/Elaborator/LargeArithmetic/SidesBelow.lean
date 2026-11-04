module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.SidesBelow

theorem sides_below :
    (2 ^ 10 : ℤ) < 1000 + 5 * 5 := by
  -- 1. arithmetic
  have s1 : (2 ^ 10 : ℤ) < 1000 + 5 * 5 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.SidesBelow
