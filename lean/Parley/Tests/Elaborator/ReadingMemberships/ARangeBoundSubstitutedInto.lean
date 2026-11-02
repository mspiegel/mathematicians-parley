module

public import LeanBridges

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundSubstitutedInto

theorem a_range_bound_substituted_into (n : ℤ) (m : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) (hH4 : n = m) :
    k ≤ m := by
  -- 1. substitute n = m (H4) into H3
  have s1 : k ≤ m := by parley_subst_at hH4 hH3
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundSubstitutedInto
