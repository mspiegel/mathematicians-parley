module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotient

theorem divide_by_a_square_of_a_quotient (j : ℤ) (hH1 : 0 < j) :
    1 / (1 / (j : ℚ)) ^ 2 = (j : ℚ) ^ 2 := by
  -- 1. algebra
  have s1 : 1 / (1 / (j : ℚ)) ^ 2 = (j : ℚ) ^ 2 := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotient
