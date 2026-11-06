module

public import OrderTactics
public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAsAFirstRow

theorem a_membership_bound_as_a_first_row (k : ℤ) (hH1 : 0 < k) :
    k + 1 ≥ 2 := by
  -- 1. inequalities
  have s1 : k + 1 ≥ 2 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundAsAFirstRow
