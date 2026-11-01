module

public import Parley.Library

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.SidesEqual

theorem sides_equal :
    (3 * 4 + 2 ^ 3 : ℤ) ≤ 20 := by
  -- 1. arithmetic
  have s1 : (3 * 4 + 2 ^ 3 : ℤ) ≤ 20 := by norm_num
  parley_side

end Parley.Tests.Elaborator.LargeArithmetic.SidesEqual
