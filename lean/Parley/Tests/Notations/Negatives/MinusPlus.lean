module

public import Parley.Library

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusPlus

theorem minus_plus :
    (-3 + 5 : ℤ) = 2 := by
  -- 1. arithmetic
  have s1 : (-3 + 5 : ℤ) = 2 := by norm_num
  parley_side

end Parley.Tests.Notations.Negatives.MinusPlus
