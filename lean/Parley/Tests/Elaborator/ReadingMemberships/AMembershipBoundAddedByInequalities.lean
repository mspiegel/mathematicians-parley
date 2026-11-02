module

public import Tactics

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAddedByInequalities

theorem a_membership_bound_added_by_inequalities (k : ℕ) (hH1 : 0 < k) :
    (k : ℤ) + 1 ≥ 2 := by
  -- 1. inequalities, from H1
  have s1 : (k : ℤ) + 1 ≥ 2 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAddedByInequalities
