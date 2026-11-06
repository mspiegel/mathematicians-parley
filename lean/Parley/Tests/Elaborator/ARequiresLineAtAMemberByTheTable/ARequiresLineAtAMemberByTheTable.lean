module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/a-requires-line-at-a-member-by-the-table.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARequiresLineAtAMemberByTheTable.ARequiresLineAtAMemberByTheTable

theorem a_requires_line_at_a_member_by_the_table (m : ℤ) (hH1 : 0 < m) (F : ℤ → ℤ) (hD1 : F 0 = (1 : ℤ) ∧ ∀ k : ℤ, 0 ≤ k → F (k + 1) = F k + 1) (hH2 : True) :
    F m + F (m + 1) = F (m + 1) + F m := by
  -- 1. algebra
  have s1 : F m + F (m + 1) = F (m + 1) + F m := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ARequiresLineAtAMemberByTheTable.ARequiresLineAtAMemberByTheTable
