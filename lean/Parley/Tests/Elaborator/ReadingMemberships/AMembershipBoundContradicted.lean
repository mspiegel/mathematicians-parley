module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted

theorem a_membership_bound_contradicted (k : ℕ) (H1 : 0 < k) :
    ¬ (k : ℤ) ≤ 0 := by
  -- 1. contradiction
  have s1 : ¬ (k : ℤ) ≤ 0 := by
    by_contra hc_S
    have S : (k : ℤ) ≤ 0 := by parley_suppose hc_S
    -- 1.1. inequalities, from S
    have s1_1 : ¬ (k : ℤ) > 0 := by linarith
    parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundContradicted
