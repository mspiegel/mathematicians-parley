module

public import Parley.Library

/-! Written from tests/elaborator/combinations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Combinations.OneMultipliedOneAdded

theorem one_multiplied_one_added (x : ℝ) (y : ℝ) (z : ℝ) (H4 : y = 1) (H5 : z = 2) :
    x * y + z = x + 2 := by
  -- 1. algebra, from H4, H5
  have s1 : x * y + z = x + 2 := by linear_combination (x) * H4 + H5
  parley_side

end Parley.Tests.Elaborator.Combinations.OneMultipliedOneAdded
