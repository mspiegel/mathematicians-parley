module

public import ArithTactics
public import Tactics

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.BothNegativeAndDenied

theorem both_negative_and_denied :
    ¬ (-3 : ℤ) ∣ (-7 : ℤ) := by
  -- 1. arithmetic
  have s1 : ¬ (-3 : ℤ) ∣ (-7 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Elaborator.SignedDivisibility.BothNegativeAndDenied
