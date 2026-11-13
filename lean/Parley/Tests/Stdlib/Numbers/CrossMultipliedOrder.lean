module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
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

namespace Parley.Tests.Stdlib.Numbers.CrossMultipliedOrder

theorem cross_multiplied_order (a : ℝ) (b : ℝ) (hH3 : b > 0) (c : ℝ) (d : ℝ) (hH6 : d > 0) :
    (a * b < c * d ↔ a / d < c / b) := by
  -- 1. mun:numbers-cross-multiplied-order, from H3, H6
  exact (Parley.Items.Stdlib.Numbers.mun_cross_multiplied_order (a := a) (b := b) hH3 (c := c) (d := d) hH6)

end Parley.Tests.Stdlib.Numbers.CrossMultipliedOrder
