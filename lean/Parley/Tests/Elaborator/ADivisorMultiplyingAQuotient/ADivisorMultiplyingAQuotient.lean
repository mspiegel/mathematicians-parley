module

public import Parley.Library

/-! Written from tests/elaborator/a-divisor-multiplying-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorMultiplyingAQuotient.ADivisorMultiplyingAQuotient

theorem a_divisor_multiplying_a_quotient (s : ℂ) (T : ℂ) (H3 : s ^ 2 = 4) (H4 : s ≠ 0) (H5 : T ≠ 0) :
    1 / (s / 2 * T) = s / (2 * T) := by
  -- 1. algebra, from H3, H4, H5
  have s1 : 1 / (s / 2 * T) = s / (2 * T) := by linear_combination (norm := parley_field) ((-(1 / 2 : ℂ)) / ((T * s))) * H3
  all_goals parley_side

end Parley.Tests.Elaborator.ADivisorMultiplyingAQuotient.ADivisorMultiplyingAQuotient
