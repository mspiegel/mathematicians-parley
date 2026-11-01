module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAsAFirstRow

theorem a_membership_bound_as_a_first_row (k : ℕ) (H1 : 0 < k) :
    (k : ℤ) + 1 ≥ 2 := by
  -- 1. inequalities
  have s1 : (k : ℤ) + 1 ≥ 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAsAFirstRow
