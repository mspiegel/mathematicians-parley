module

public import ArithTactics
public import Tactics

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.TwoCubed

theorem two_cubed :
    (2 ^ 3 : ℤ) = 8 := by
  -- 1. arithmetic
  have s1 : (2 ^ 3 : ℤ) = 8 := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Numbers.TwoCubed
