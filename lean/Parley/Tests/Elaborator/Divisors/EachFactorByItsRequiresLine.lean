module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/divisors.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Divisors.EachFactorByItsRequiresLine

theorem each_factor_by_its_requires_line (x : ℝ) (y : ℝ) (hH3 : x ≠ 0) (hH4 : y ≠ 0) :
    (2 * x * y + 3) / (x * y) = 2 + 3 / (x * y) := by
  -- 1. algebra
  have r20_1 : x ≠ 0 := by parley_side
  have r20_2 : y ≠ 0 := by parley_side
  have s1 : (2 * x * y + 3) / (x * y) = 2 + 3 / (x * y) := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.Divisors.EachFactorByItsRequiresLine
