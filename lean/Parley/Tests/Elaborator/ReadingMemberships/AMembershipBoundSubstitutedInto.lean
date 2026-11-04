module

public import SubstTactics
public import Tactics

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto

theorem a_membership_bound_substituted_into (k : ℕ) (hH1 : 0 < k) (m : ℤ) (hH3 : (k : ℤ) = m) :
    m > 0 := by
  -- 1. substitute k = m (H3) into H1
  have s1 : m > 0 := by parley_subst_at hH3 hH1
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundSubstitutedInto
