module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.ANegativeTurned

theorem a_negative_turned (x : ℝ) (hH2 : x < 0) :
    0 < -x := by
  -- 1. inequalities
  have s1 : 0 < -x := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.InequalityRows.ANegativeTurned
