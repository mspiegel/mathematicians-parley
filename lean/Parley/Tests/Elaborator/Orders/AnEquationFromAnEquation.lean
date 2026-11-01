module

public import Parley.Library

/-! Written from tests/elaborator/orders.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Orders.AnEquationFromAnEquation

theorem an_equation_from_an_equation (x : ℝ) (H2 : x = 2) :
    2 * x = 4 := by
  -- 1. inequalities
  have s1 : 2 * x = 4 := by parley_side
  parley_side

end Parley.Tests.Elaborator.Orders.AnEquationFromAnEquation
