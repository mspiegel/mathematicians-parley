module

public import Parley.Library

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.TwoCubed

theorem two_cubed :
    (2 ^ 3 : ℤ) = 8 := by
  -- 1. arithmetic
  have s1 : (2 ^ 3 : ℤ) = 8 := by norm_num
  parley_side

end Parley.Tests.Notations.Numbers.TwoCubed
