module

public import Parley.Library

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAProductWithAQuotient

theorem divide_by_a_product_with_a_quotient (j : ℕ) (H1 : 0 < j) :
    1 / (2 * (1 / (j : ℚ))) = (j : ℚ) / 2 := by
  -- 1. algebra
  have s1 : 1 / (2 * (1 / (j : ℚ))) = (j : ℚ) / 2 := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByAProductWithAQuotient
