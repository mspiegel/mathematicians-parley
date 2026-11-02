module

public import Tactics

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.ACubeMultipliedOut

theorem a_cube_multiplied_out (x : ℝ) :
    (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by
  -- 1. algebra
  have s1 : (x + 1) ^ 3 = x ^ 3 + 3 * x ^ 2 + 3 * x + 1 := by parley_ring
  all_goals parley_side

end Parley.Tests.Notations.Numbers.ACubeMultipliedOut
