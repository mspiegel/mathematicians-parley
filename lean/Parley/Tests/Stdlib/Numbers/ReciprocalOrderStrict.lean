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
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ReciprocalOrderStrict

theorem reciprocal_order_strict (x : ℝ) (hH2 : x > 0) (y : ℝ) (hH4 : y > 0) :
    (x < y ↔ 1 / y < 1 / x) := by
  -- 1. mun:numbers-reciprocal-order-strict, from H2, H4
  exact (Parley.Items.Stdlib.Numbers.mun_reciprocal_order_strict (x := x) hH2 (y := y) hH4)

end Parley.Tests.Stdlib.Numbers.ReciprocalOrderStrict
