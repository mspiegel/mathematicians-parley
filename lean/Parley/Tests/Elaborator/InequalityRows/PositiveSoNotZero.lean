module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero

theorem positive_so_not_zero (x : ℝ) (hH2 : 0 < x) :
    x ≠ 0 := by
  -- 1. inequalities
  parley_side

end Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero
