module

public import LeanBridges

/-! Written from tests/notations/negatives.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Negatives.MinusHalfBelowZero

theorem minus_half_below_zero :
    (-(1 / 2) : ℚ) < 0 := by
  -- 1. arithmetic
  have s1 : (-(1 / 2) : ℚ) < 0 := by parley_arith
  all_goals parley_side

end Parley.Tests.Notations.Negatives.MinusHalfBelowZero
