module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/divisor-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.DivisorOrder.ASignNamedBeforeAnUncitedLine

theorem a_sign_named_before_an_uncited_line (x : ℝ) (hH2 : x > 0) (hH3 : x ≠ 0) :
    1 / x * x = 1 := by
  -- 1. algebra, from H2
  have s1 : 1 / x * x = 1 := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.DivisorOrder.ASignNamedBeforeAnUncitedLine
