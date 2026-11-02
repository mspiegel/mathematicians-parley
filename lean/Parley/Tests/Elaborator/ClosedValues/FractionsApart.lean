module

public import LeanBridges

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.FractionsApart

theorem fractions_apart :
    (17 / (3 * 2) / 65 : ℚ) ≠ 2 := by
  -- 1. arithmetic
  have s1 : (17 / (3 * 2) / 65 : ℚ) ≠ 2 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.ClosedValues.FractionsApart
