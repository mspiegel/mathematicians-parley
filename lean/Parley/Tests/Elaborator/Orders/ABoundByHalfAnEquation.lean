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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/orders.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Orders.ABoundByHalfAnEquation

theorem a_bound_by_half_an_equation (x : ℝ) (hH2 : 2 * x = 3) :
    x ≤ 3 / 2 := by
  -- 1. inequalities
  linarith only [hH2]

end Parley.Tests.Elaborator.Orders.ABoundByHalfAnEquation
