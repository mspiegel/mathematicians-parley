module

public import Parley.Library

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.ZeroNotBelowMinusOne

theorem zero_not_below_minus_one :
    ¬ (0 : ℤ) < -1 := by
  -- 1. arithmetic
  have s1 : ¬ (0 : ℤ) < -1 := by norm_num
  parley_side

end Parley.Tests.Notations.Negatives.ZeroNotBelowMinusOne
