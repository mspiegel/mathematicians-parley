module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Init
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/a-quotient-divisor-said-not-zero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AQuotientDivisorSaidNotZero.AQuotientDivisorSaidNotZero

theorem a_quotient_divisor_said_not_zero (ε : ℝ) (d : ℝ) (n : ℤ) (hH3 : 0 < n) (hH4 : ε / (2 * d) > 0) (hH5 : 1 / (n : ℚ) > 0) (hH6 : d > 0) :
    0 - ε / (2 * d) < 1 / (n : ℝ) := by
  -- 1. inequalities
  have s1 : 2 * d ≠ 0 := ne_of_gt (by linarith only [hH6])
  -- 2. inequalities
  have r17_1 : 2 * d ≠ 0 := by exact s1
  have s2 : 0 - ε / (2 * d) < 0 := by linarith only [hH4]
  -- 3. transitivity, from 2, H5
  have r23_1 : 2 * d ≠ 0 := by exact s1
  parley_order

end Parley.Tests.Elaborator.AQuotientDivisorSaidNotZero.AQuotientDivisorSaidNotZero
