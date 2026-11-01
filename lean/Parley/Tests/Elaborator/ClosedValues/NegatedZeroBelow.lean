module

public import Parley.Library

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.NegatedZeroBelow

theorem negated_zero_below :
    (-0 : ℤ) ≤ 64 := by
  -- 1. arithmetic
  have s1 : (-0 : ℤ) ≤ 64 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.ClosedValues.NegatedZeroBelow
