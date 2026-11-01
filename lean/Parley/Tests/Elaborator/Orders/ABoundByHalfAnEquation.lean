module

public import Parley.Library

/-! Written from tests/elaborator/orders.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Orders.ABoundByHalfAnEquation

theorem a_bound_by_half_an_equation (x : ℝ) (hH2 : 2 * x = 3) :
    x ≤ 3 / 2 := by
  -- 1. inequalities
  have s1 : x ≤ 3 / 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.Orders.ABoundByHalfAnEquation
