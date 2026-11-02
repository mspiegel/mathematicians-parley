module

public import LeanBridges

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotientScaled

theorem divide_by_a_square_of_a_quotient_scaled (j : ℕ) (hH1 : 0 < j) :
    2 / (1 / (j : ℚ)) ^ 2 = 2 * (j : ℚ) ^ 2 := by
  -- 1. algebra
  have s1 : 2 / (1 / (j : ℚ)) ^ 2 = 2 * (j : ℚ) ^ 2 := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.DivideByACompoundQuotient.DivideByASquareOfAQuotientScaled
