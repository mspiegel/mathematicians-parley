module

public import Parley.Library

/-! Written from tests/elaborator/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Powers.APowerOfPowers

theorem a_power_of_powers (x : ℝ) :
    ((x ^ 3) ^ 3) ^ 3 = x ^ 27 := by
  -- 1. algebra
  have s1 : ((x ^ 3) ^ 3) ^ 3 = x ^ 27 := by ring
  parley_side

end Parley.Tests.Elaborator.Powers.APowerOfPowers
