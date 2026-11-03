module

public import Tactics

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundAsAFirstRow

theorem a_range_bound_as_a_first_row (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) :
    k + 1 ≤ n + 1 := by
  -- 1. inequalities
  have s1 : k + 1 ≤ n + 1 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundAsAFirstRow
