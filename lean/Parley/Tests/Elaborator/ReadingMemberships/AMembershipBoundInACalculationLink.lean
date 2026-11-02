module

public import LeanBridges

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink

theorem a_membership_bound_in_a_calculation_link (k : ℕ) (hH1 : 0 < k) (m : ℤ) (hH3 : (k : ℤ) ≤ m) :
    0 < m := by
  -- 1. calculation
  have s1 : 0 < m := by
    calc (0 : ℤ) < (k : ℤ) := by parley_side
      _ ≤ m := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink
