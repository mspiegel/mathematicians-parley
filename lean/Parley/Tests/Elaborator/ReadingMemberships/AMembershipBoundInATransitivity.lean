module

public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInATransitivity

theorem a_membership_bound_in_a_transitivity (c : ℤ) (hH1 : 0 ≤ c) (m : ℤ) (hH3 : c ≤ m) :
    0 ≤ m := by
  -- 1. transitivity, from H1, H3
  have s1 : 0 ≤ m := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInATransitivity
