module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.AProductWrittenNotZero

theorem a_product_written_not_zero (x : ℝ) (y : ℝ) (hH3 : x * y ≠ 0) :
    (2 * x * y + 3) / (x * y) = 2 + 3 / (x * y) := by
  -- 1. algebra
  have r8_1 : x * y ≠ 0 := by exact hH3
  parley_ring

end Parley.Tests.Elaborator.Divisors.AProductWrittenNotZero
