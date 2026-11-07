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
  have s1 : x ≠ 0 := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero
