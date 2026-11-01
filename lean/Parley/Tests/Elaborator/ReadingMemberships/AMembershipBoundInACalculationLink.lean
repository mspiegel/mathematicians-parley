module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink

theorem a_membership_bound_in_a_calculation_link (k : ℕ) (H1 : 0 < k) (m : ℤ) (H3 : (k : ℤ) ≤ m) :
    0 < m := by
  -- 1. calculation
  have s1 : 0 < m := by
    calc 0 < (k : ℤ) := by parley_side
      _ ≤ m := by parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink
