module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.PowerOfANegativeBase

theorem power_of_a_negative_base :
    ((-2) ^ 2 : ℤ) < (-2) ^ 2 + 19 := by
  -- 1. arithmetic
  have s1 : ((-2) ^ 2 : ℤ) < (-2) ^ 2 + 19 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ClosedValues.PowerOfANegativeBase
