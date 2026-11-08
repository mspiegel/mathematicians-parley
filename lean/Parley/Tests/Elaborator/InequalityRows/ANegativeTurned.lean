module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.ANegativeTurned

theorem a_negative_turned (x : ℝ) (hH2 : x < 0) :
    0 < -x := by
  -- 1. inequalities
  parley_order

end Parley.Tests.Elaborator.InequalityRows.ANegativeTurned
