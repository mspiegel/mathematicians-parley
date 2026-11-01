module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/a-cancelled-factor-against-a-dropped-one.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheRight

theorem the_one_dropped_on_the_right (x : ℝ) (k : ℝ) (hH3 : x ≠ 0) (hH4 : 2 * k * x = x) :
    2 * k = 1 := by
  -- 1. mun:multiply-cancel a := 2·k, b := 1, c := x, from H3, H4
  have s1 : 2 * k = 1 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side))
  all_goals parley_side

end Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheRight
