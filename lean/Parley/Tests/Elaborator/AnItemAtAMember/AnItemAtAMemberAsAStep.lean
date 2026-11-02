module

public import LeanBridges
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/an-item-at-a-member.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnItemAtAMember.AnItemAtAMemberAsAStep

theorem an_item_at_a_member_as_a_step (B : ℤ → ℝ) :
    True := by
  -- 1. mun:sum-real a := 1, b := m
  all_goals parley_side

end Parley.Tests.Elaborator.AnItemAtAMember.AnItemAtAMemberAsAStep
