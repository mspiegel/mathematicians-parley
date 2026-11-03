module

public import Tactics

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusTimesMinus

theorem minus_times_minus :
    (-1 * -1 : ℤ) = 1 := by
  -- 1. arithmetic
  have s1 : (-1 * -1 : ℤ) = 1 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Negatives.MinusTimesMinus
