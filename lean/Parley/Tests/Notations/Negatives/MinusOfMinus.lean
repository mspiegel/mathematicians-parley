module

public import Parley.Library

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusOfMinus

theorem minus_of_minus :
    (-(-3) : ℤ) = 3 := by
  -- 1. arithmetic
  have s1 : (-(-3) : ℤ) = 3 := by norm_num
  parley_side

end Parley.Tests.Notations.Negatives.MinusOfMinus
