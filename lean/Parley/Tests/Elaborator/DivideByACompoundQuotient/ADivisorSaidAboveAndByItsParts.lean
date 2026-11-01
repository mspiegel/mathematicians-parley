module

public import Parley.Library

/-! Written from tests/elaborator/divide-by-a-compound-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivideByACompoundQuotient.ADivisorSaidAboveAndByItsParts

theorem a_divisor_said_above_and_by_its_parts (x : ℝ) (hH2 : x ≠ 0) (hH3 : 1 / x ≠ 0) :
    1 / (1 / x) = x := by
  -- 1. algebra, from H2
  have s1 : 1 / (1 / x) = x := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.DivideByACompoundQuotient.ADivisorSaidAboveAndByItsParts
