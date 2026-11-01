module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted

theorem a_membership_bound_contradicted (k : ℕ) (hH1 : 0 < k) :
    ¬ (k : ℤ) ≤ 0 := by
  -- 1. contradiction
  have s1 : ¬ (k : ℤ) ≤ 0 := by
    by_contra hc_hS
    have hS : (k : ℤ) ≤ 0 := by parley_suppose hc_hS
    -- 1.1. inequalities, from S
    have s1_1 : ¬ (k : ℤ) > 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted
