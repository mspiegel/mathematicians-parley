module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LessScaled

theorem less_scaled (x : ℝ) (y : ℝ) (c : ℝ) (hH4 : c > 0) :
    (x < y ↔ c * x < c * y) := by
  -- 1. mun:numbers-less-scaled, from H4
  exact (Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) hH4)

end Parley.Tests.Stdlib.Numbers.LessScaled
