module

public import Tactics

/-! Written from tests/elaborator/an-nth-derivative.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower

theorem a_number_to_a_bracketed_power (x : ℝ) (n : ℕ) (hH2 : 0 < n) :
    x ^ n = x ^ n := by
  -- 1. algebra
  have s1 : x ^ n = x ^ n := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower
