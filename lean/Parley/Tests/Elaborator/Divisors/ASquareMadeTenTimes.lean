module

public import Parley.Library

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.ASquareMadeTenTimes

theorem a_square_made_ten_times (x : ℝ) (z : ℝ) (H3 : x ^ 2 ≠ 0) :
    (1 / 10 * x ^ 3 + z) / x ^ 2 = (1 / 10 * x ^ 3 + z) / x ^ 2 := by
  -- 1. algebra
  have r32_1 : x ^ 2 ≠ 0 := by parley_side
  have s1 : (1 / 10 * x ^ 3 + z) / x ^ 2 = (1 / 10 * x ^ 3 + z) / x ^ 2 := by parley_ring
  parley_side

end Parley.Tests.Elaborator.Divisors.ASquareMadeTenTimes
