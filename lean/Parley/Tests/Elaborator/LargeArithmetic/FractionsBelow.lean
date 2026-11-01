module

public import Parley.Library

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.FractionsBelow

theorem fractions_below :
    (2 / 3 : ℚ) < 5 / 7 := by
  -- 1. arithmetic
  have s1 : (2 / 3 : ℚ) < 5 / 7 := by norm_num
  parley_side

end Parley.Tests.Elaborator.LargeArithmetic.FractionsBelow
