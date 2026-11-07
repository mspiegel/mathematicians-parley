module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divisor-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorOrder.APowerToZeroDivisor

theorem a_power_to_zero_divisor (x : ℝ) (hH2 : x ≠ 0) :
    1 / x ^ 0 = 1 := by
  -- 1. algebra, from H2
  have s1 : 1 / x ^ 0 = 1 := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivisorOrder.APowerToZeroDivisor
