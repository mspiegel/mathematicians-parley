module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.AnEquationReadAsAnOrder

theorem an_equation_read_as_an_order (x : ℝ) (y : ℝ) (hH3 : y = x) :
    x ≤ y := by
  -- 1. inequalities
  have s1 : x ≤ y := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.InequalityRows.AnEquationReadAsAnOrder
