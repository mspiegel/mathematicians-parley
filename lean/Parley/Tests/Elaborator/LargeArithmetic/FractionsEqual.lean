module

public import Parley.Library

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual

theorem fractions_equal :
    (2 / 4 : ℚ) ≤ 3 / 6 := by
  -- 1. arithmetic
  have s1 : (2 / 4 : ℚ) ≤ 3 / 6 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.LargeArithmetic.FractionsEqual
