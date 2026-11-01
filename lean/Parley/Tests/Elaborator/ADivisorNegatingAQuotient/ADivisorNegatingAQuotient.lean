module

public import Parley.Library

/-! Written from tests/elaborator/a-divisor-negating-a-quotient.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ADivisorNegatingAQuotient.ADivisorNegatingAQuotient

theorem a_divisor_negating_a_quotient (x : ℝ) (H2 : -(x / 2) ≠ 0) :
    x / -(x / 2) = -2 := by
  -- 1. algebra
  have r9_1 : -(x / 2) ≠ 0 := by parley_side
  have s1 : x / -(x / 2) = -2 := by parley_ring
  parley_side

end Parley.Tests.Elaborator.ADivisorNegatingAQuotient.ADivisorNegatingAQuotient
