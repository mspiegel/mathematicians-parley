module

public import ArithTactics
public import Tactics

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.TwoDoesNotDivideSeven

theorem two_does_not_divide_seven :
    ¬ (2 : ℤ) ∣ (7 : ℤ) := by
  -- 1. arithmetic
  have s1 : ¬ (2 : ℤ) ∣ (7 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Divisibility.TwoDoesNotDivideSeven
