module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundReadByTheMembershipMethod

theorem a_membership_bound_read_by_the_membership_method (x : ℝ) (x : ℕ) (H2 : 0 < x) :
    True := by
  -- 1. membership, from H2
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundReadByTheMembershipMethod
