module

public import Tactics

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusOfMinus

theorem minus_of_minus :
    (-(-3) : ℤ) = 3 := by
  -- 1. arithmetic
  have s1 : (-(-3) : ℤ) = 3 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Negatives.MinusOfMinus
