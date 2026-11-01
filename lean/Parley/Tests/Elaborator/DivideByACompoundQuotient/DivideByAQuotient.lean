module

public import Parley.Library

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAQuotient

theorem divide_by_a_quotient (x : ℝ) (H2 : x ≠ 0) :
    1 / (1 / x) = x := by
  -- 1. algebra, from H2
  have s1 : 1 / (1 / x) = x := by parley_ring
  parley_side

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAQuotient
