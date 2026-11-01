module

public import Parley.Library

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto

theorem a_membership_bound_substituted_into (k : ℕ) (H1 : 0 < k) (m : ℤ) (H3 : (k : ℤ) = m) :
    m > 0 := by
  -- 1. substitute k = m (H3) into H1
  have s1 : m > 0 := by parley_subst_at H3 H1
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto
