module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.AFourthPowerOfASquare

theorem a_fourth_power_of_a_square (x : ℝ) :
    x ^ 4 = (x ^ 2) ^ 2 := by
  -- 1. algebra
  have s1 : x ^ 4 = (x ^ 2) ^ 2 := by parley_ring
  all_goals exact s1

end Parley.Tests.Notations.Numbers.AFourthPowerOfASquare
