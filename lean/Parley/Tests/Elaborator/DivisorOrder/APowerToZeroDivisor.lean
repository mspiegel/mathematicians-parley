module

public import Parley.Library

/-! Written from tests/elaborator/divisor-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorOrder.APowerToZeroDivisor

theorem a_power_to_zero_divisor (x : ℝ) (H2 : x ≠ 0) :
    1 / x ^ 0 = 1 := by
  -- 1. algebra, from H2
  have s1 : 1 / x ^ 0 = 1 := by parley_ring
  parley_side

end Parley.Tests.Elaborator.DivisorOrder.APowerToZeroDivisor
