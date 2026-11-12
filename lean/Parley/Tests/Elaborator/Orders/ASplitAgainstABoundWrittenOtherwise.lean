module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/orders.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Orders.ASplitAgainstABoundWrittenOtherwise

theorem a_split_against_a_bound_written_otherwise (x : ℝ) (hH2 : 2 * x ≤ 4) (hH3 : x ≠ 2) :
    x < 2 := by
  -- 1. inequalities
  have s1 : x ≤ 2 := by linarith only [hH2]
  -- 2. inequalities, from H3, 1
  exact Or.elim (Ne.lt_or_gt hH3) (fun h1 => by linarith only [s1, h1]) (fun h1 => by linarith only [s1, h1])

end Parley.Tests.Elaborator.Orders.ASplitAgainstABoundWrittenOtherwise
