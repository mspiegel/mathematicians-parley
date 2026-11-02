module

public import Tactics

/-! Written from tests/elaborator/orders.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Orders.ASplitAgainstABoundWrittenOtherwise

theorem a_split_against_a_bound_written_otherwise (x : ℝ) (hH2 : 2 * x ≤ 4) (hH3 : x ≠ 2) :
    x < 2 := by
  -- 1. inequalities
  have s1 : x ≤ 2 := by parley_order
  -- 2. inequalities, from H3, 1
  have s2 : x < 2 := by parley_order
  all_goals parley_side

end Parley.Tests.Elaborator.Orders.ASplitAgainstABoundWrittenOtherwise
