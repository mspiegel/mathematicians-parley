module

public import Parley.Library

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.DividedByANegativeFraction

theorem divided_by_a_negative_fraction :
    (8 / -(2 / 3) : ℚ) = -12 := by
  -- 1. arithmetic
  have s1 : (8 / -(2 / 3) : ℚ) = -12 := by norm_num
  parley_side

end Parley.Tests.Elaborator.ClosedValues.DividedByANegativeFraction
