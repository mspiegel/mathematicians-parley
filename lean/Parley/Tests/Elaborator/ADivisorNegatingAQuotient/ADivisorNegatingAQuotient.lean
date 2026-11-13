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

/-! Written from tests/elaborator/a-divisor-negating-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorNegatingAQuotient.ADivisorNegatingAQuotient

theorem a_divisor_negating_a_quotient (x : ℝ) (hH2 : -(x / 2) ≠ 0) :
    x / -(x / 2) = -2 := by
  -- 1. algebra
  have r9_1 : -(x / 2) ≠ 0 := by exact hH2
  parley_ring

end Parley.Tests.Elaborator.ADivisorNegatingAQuotient.ADivisorNegatingAQuotient
