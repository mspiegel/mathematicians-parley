module

public import LeanBridges

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.WholeInTheRationals

theorem whole_in_the_rationals :
    True := by
  -- 1. arithmetic
  all_goals parley_side

end Parley.Tests.Elaborator.ClosedValues.WholeInTheRationals
