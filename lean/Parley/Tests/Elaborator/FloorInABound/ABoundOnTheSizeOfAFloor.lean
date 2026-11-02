module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/floor-in-a-bound.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.FloorInABound.ABoundOnTheSizeOfAFloor

theorem a_bound_on_the_size_of_a_floor (A : ℝ) (hH2 : abs ⌊A⌋ = ⌊A⌋) (hH3 : ⌊A⌋ ≤ 1) :
    abs ⌊A⌋ ≤ 1 := by
  -- 1. mun:floor-integer x := A
  -- 2. membership, from 1
  -- 3. transitivity, from H2, H3
  have s3 : abs ⌊A⌋ ≤ 1 := by parley_order
  all_goals parley_side

end Parley.Tests.Elaborator.FloorInABound.ABoundOnTheSizeOfAFloor
