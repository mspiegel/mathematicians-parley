module

public import Tactics

/-! Written from tests/elaborator/a-for-all-line-read-in-a-block.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineJoinedInABlock

theorem a_for_all_line_joined_in_a_block :
    (∀ z : ℤ, z * 1 = z) := by
  -- 1. proof
  have s1 : ∀ x : ℤ, x * 1 = x := by
    intro x
    -- 1.1. algebra
    have s1_1 : x * 1 = x := by parley_ring
    all_goals parley_side
  -- 2. proof
  have s2 : ∀ z : ℤ, z * 1 = z := by
    intro z
    -- 2.1. restate 1
    have s2_1 : z * 1 = z := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AForAllLineReadInABlock.AForAllLineJoinedInABlock
