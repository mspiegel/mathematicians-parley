module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/an-nth-derivative.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower

theorem a_number_to_a_bracketed_power (x : ℝ) (n : ℤ) (hH2 : 0 < n) :
    x ^ n.toNat = x ^ n.toNat := by
  -- 1. algebra
  have s1 : x ^ n.toNat = x ^ n.toNat := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.AnNthDerivative.ANumberToABracketedPower
