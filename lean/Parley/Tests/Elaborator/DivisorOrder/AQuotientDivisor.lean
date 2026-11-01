module

public import Parley.Library

/-! Written from tests/elaborator/divisor-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorOrder.AQuotientDivisor

theorem a_quotient_divisor (x : ℝ) (hH2 : x ≠ 0) :
    1 / (x / 2) = 2 / x := by
  -- 1. algebra, from H2
  have s1 : 1 / (x / 2) = 2 / x := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.DivisorOrder.AQuotientDivisor
