module

public import Tactics

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeDivisor

theorem a_negative_divisor :
    (-3 : ℤ) ∣ (9 : ℤ) := by
  -- 1. arithmetic
  have s1 : (-3 : ℤ) ∣ (9 : ℤ) := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeDivisor
