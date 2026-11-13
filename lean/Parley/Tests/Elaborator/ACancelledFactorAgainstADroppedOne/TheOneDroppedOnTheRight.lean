module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-cancelled-factor-against-a-dropped-one.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheRight

theorem the_one_dropped_on_the_right (x : ℝ) (k : ℝ) (hH3 : x ≠ 0) (hH4 : 2 * k * x = x) :
    2 * k = 1 := by
  -- 1. mun:multiply-cancel a := 2·k, b := 1, c := x, from H3, H4
  exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by simpa only [one_mul] using hH4) hH3)

end Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheRight
