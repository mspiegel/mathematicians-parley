module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-cancelled-factor-against-a-dropped-one.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheLeft

theorem the_one_dropped_on_the_left (x : ℝ) (k : ℝ) (hH3 : x ≠ 0) (hH4 : x = k * x) :
    1 = k := by
  -- 1. mun:multiply-cancel a := 1, b := k, c := x, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := (1 : ℝ)) (b := k) (c := x) (by parley_side) (by parley_side))

end Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheLeft
