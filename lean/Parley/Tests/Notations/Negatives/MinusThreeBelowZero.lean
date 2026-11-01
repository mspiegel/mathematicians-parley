module

public import Parley.Library

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusThreeBelowZero

theorem minus_three_below_zero :
    (-3 : ℤ) < 0 := by
  -- 1. arithmetic
  have s1 : (-3 : ℤ) < 0 := by norm_num
  parley_side

end Parley.Tests.Notations.Negatives.MinusThreeBelowZero
