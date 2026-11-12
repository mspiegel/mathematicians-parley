module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.AnEquationReadAsAnOrder

theorem an_equation_read_as_an_order (x : ℝ) (y : ℝ) (hH3 : y = x) :
    x ≤ y := by
  -- 1. inequalities
  linarith only [hH3]

end Parley.Tests.Elaborator.InequalityRows.AnEquationReadAsAnOrder
