module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAddedByInequalities

theorem a_membership_bound_added_by_inequalities (k : ℤ) (hH1 : 0 < k) :
    k + 1 ≥ 2 := by
  -- 1. inequalities, from H1
  have s1 : k + 1 ≥ 2 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAddedByInequalities
