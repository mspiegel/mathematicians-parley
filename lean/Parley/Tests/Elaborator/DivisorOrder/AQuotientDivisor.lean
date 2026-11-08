module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/divisor-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorOrder.AQuotientDivisor

theorem a_quotient_divisor (x : ℝ) (hH2 : x ≠ 0) :
    1 / (x / 2) = 2 / x := by
  -- 1. algebra, from H2
  parley_ring

end Parley.Tests.Elaborator.DivisorOrder.AQuotientDivisor
