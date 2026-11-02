module

public import LeanBridges

/-! Written from tests/elaborator/a-range-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeMemberIsCited.ARangeMemberIsCited

theorem a_range_member_is_cited (N : ℕ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) (N : ℤ)) :
    (LeanBridges.Counting.choose (N : ℤ) k : ℤ) * 1 = (LeanBridges.Counting.choose (N : ℤ) k : ℤ) := by
  -- 1. algebra
  have s1 : (LeanBridges.Counting.choose (N : ℤ) k : ℤ) * 1 = (LeanBridges.Counting.choose (N : ℤ) k : ℤ) := by parley_ring
  all_goals parley_side

end Parley.Tests.Elaborator.ARangeMemberIsCited.ARangeMemberIsCited
