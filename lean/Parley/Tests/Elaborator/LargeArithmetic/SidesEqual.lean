module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.SidesEqual

theorem sides_equal :
    (3 * 4 + 2 ^ 3 : ℤ) ≤ 20 := by
  -- 1. arithmetic
  have s1 : (3 * 4 + 2 ^ 3 : ℤ) ≤ 20 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.SidesEqual
