module

public import AlgebraTactics
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/divisor-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorOrder.ANegationDivisor

theorem a_negation_divisor (x : ℝ) (hH2 : x ≠ 0) (hH3 : -x ≠ 0) :
    1 / -x = -(1 / x) := by
  -- 1. algebra, from H2
  parley_ring

end Parley.Tests.Elaborator.DivisorOrder.ANegationDivisor
