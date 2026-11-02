module

public import Tactics

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundAddedByInequalities

theorem a_range_bound_added_by_inequalities (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) :
    k < n + 1 := by
  -- 1. inequalities, from H2
  have s1 : k < n + 1 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundAddedByInequalities
