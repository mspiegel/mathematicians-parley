module

public import Parley.Library

/-! Written from tests/elaborator/orders.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Orders.ASplitAgainstABoundWrittenOtherwise

theorem a_split_against_a_bound_written_otherwise (x : ℝ) (H2 : 2 * x ≤ 4) (H3 : x ≠ 2) :
    x < 2 := by
  -- 1. inequalities
  have s1 : x ≤ 2 := by parley_side
  -- 2. inequalities, from H3, 1
  have s2 : x < 2 := by parley_side
  parley_side

end Parley.Tests.Elaborator.Orders.ASplitAgainstABoundWrittenOtherwise
