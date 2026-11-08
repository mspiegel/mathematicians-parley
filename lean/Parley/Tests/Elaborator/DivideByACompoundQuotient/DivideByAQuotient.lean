module

public import AlgebraTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAQuotient

theorem divide_by_a_quotient (x : ℝ) (hH2 : x ≠ 0) :
    1 / (1 / x) = x := by
  -- 1. algebra, from H2
  parley_ring

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAQuotient
