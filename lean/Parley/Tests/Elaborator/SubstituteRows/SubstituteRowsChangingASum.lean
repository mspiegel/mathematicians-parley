module

public import AlgebraTactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/substitute-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsChangingASum

theorem substitute_rows_changing_a_sum (a : ℝ) (b : ℝ) (hH3 : a * 2 + b * 2 < 1) :
    2 * a + 2 * b < 1 := by
  -- 1. substitute
  have c1 : a * 2 + b * 2 = 2 * a + 2 * b := by parley_ring
  have row1 : 2 * a + 2 * b < 1 := Eq.subst (motive := (fun t : ℝ => t < 1)) c1 hH3
  exact row1

end Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsChangingASum
