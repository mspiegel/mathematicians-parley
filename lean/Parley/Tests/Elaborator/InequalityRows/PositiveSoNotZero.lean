module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero

theorem positive_so_not_zero (x : ℝ) (hH2 : 0 < x) :
    x ≠ 0 := by
  -- 1. inequalities
  linarith only [hH2]

end Parley.Tests.Elaborator.InequalityRows.PositiveSoNotZero
