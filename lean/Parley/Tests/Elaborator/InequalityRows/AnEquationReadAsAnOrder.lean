module

public import Tactics

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.AnEquationReadAsAnOrder

theorem an_equation_read_as_an_order (x : ℝ) (y : ℝ) (hH3 : y = x) :
    x ≤ y := by
  -- 1. inequalities
  have s1 : x ≤ y := by parley_order
  all_goals parley_side

end Parley.Tests.Elaborator.InequalityRows.AnEquationReadAsAnOrder
