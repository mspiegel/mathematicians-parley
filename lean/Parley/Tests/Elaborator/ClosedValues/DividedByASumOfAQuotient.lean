module

public import Tactics

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.DividedByASumOfAQuotient

theorem divided_by_a_sum_of_a_quotient :
    (1 / (9 - 0 / 7) : ℚ) = 1 / 9 := by
  -- 1. arithmetic
  have s1 : (1 / (9 - 0 / 7) : ℚ) = 1 / 9 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.ClosedValues.DividedByASumOfAQuotient
