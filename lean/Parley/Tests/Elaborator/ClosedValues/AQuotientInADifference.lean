module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.AQuotientInADifference

theorem a_quotient_in_a_difference :
    ((7 + 8) / 1 - 2 : ℚ) < 19 := by
  -- 1. arithmetic
  have s1 : ((7 + 8) / 1 - 2 : ℚ) < 19 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ClosedValues.AQuotientInADifference
