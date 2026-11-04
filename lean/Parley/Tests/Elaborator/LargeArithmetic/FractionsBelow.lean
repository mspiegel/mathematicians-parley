module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionsBelow

theorem fractions_below :
    (2 / 3 : ℚ) < 5 / 7 := by
  -- 1. arithmetic
  have s1 : (2 / 3 : ℚ) < 5 / 7 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.LargeArithmetic.FractionsBelow
