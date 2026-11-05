module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/closed-values.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ClosedValues.ARemainderInAQuotient

theorem a_remainder_in_a_quotient :
    -6 ≠ 536 * (((2 : ℤ) % (216 : ℤ) : ℤ) : ℚ) / 1 := by
  -- 1. arithmetic
  have s1 : -6 ≠ 536 * (((2 : ℤ) % (216 : ℤ) : ℤ) : ℚ) / 1 := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.ClosedValues.ARemainderInAQuotient
