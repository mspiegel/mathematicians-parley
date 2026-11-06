module

public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink

theorem a_membership_bound_in_a_calculation_link (k : ℤ) (hH1 : 0 < k) (m : ℤ) (hH3 : k ≤ m) :
    0 < m := by
  -- 1. calculation
  have s1 : 0 < m := by
    calc (0 : ℤ) < k := by parley_side
      _ ≤ m := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInACalculationLink
