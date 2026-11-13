module

public import AlgebraTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Defs.PartialOrder
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

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.ADivisorNotZeroByWeakening

theorem a_divisor_not_zero_by_weakening (p : ℝ) (q : ℝ) (hH3 : q > 0) :
    p / q * q = p := by
  -- 1. algebra
  have r50_1 : q ≠ 0 := ne_of_gt (by linarith only [hH3])
  parley_ring

end Parley.Tests.Elaborator.InequalityRows.ADivisorNotZeroByWeakening
