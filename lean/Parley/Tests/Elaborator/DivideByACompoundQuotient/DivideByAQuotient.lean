module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAQuotient

theorem divide_by_a_quotient (x : ℝ) (hH2 : x ≠ 0) :
    1 / (1 / x) = x := by
  -- 1. algebra, from H2
  have s1 : 1 / (1 / x) = x := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAQuotient
