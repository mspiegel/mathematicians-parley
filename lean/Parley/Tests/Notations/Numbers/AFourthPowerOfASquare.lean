module

public import Parley.Library

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.AFourthPowerOfASquare

theorem a_fourth_power_of_a_square (x : ℝ) :
    x ^ 4 = (x ^ 2) ^ 2 := by
  -- 1. algebra
  have s1 : x ^ 4 = (x ^ 2) ^ 2 := by ring
  all_goals parley_side

end Parley.Tests.Notations.Numbers.AFourthPowerOfASquare
