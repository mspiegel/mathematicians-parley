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

namespace Parley.Tests.Elaborator.DivisorOrder.ANegationDivisor

theorem a_negation_divisor (x : ℝ) (hH2 : x ≠ 0) (hH3 : -x ≠ 0) :
    1 / -x = -(1 / x) := by
  -- 1. algebra, from H2
  have s1 : 1 / -x = -(1 / x) := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivisorOrder.ANegationDivisor
