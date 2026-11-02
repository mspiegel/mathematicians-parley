module

public import LeanBridges

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInATransitivity

theorem a_membership_bound_in_a_transitivity (c : ℕ) (m : ℤ) (hH3 : (c : ℤ) ≤ m) :
    0 ≤ m := by
  -- 1. transitivity, from H1, H3
  have s1 : 0 ≤ m := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInATransitivity
