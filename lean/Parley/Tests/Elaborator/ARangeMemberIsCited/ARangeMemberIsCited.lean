module

public import AlgebraTactics
public import Counting
public import FactorialTactics
public import Tactics

/-! Written from tests/elaborator/a-range-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeMemberIsCited.ARangeMemberIsCited

theorem a_range_member_is_cited (N : ℤ) (hH1 : 0 ≤ N) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) N) :
    (LeanBridges.Counting.choose N k : ℤ) * 1 = (LeanBridges.Counting.choose N k : ℤ) := by
  -- 1. algebra
  have s1 : (LeanBridges.Counting.choose N k : ℤ) * 1 = (LeanBridges.Counting.choose N k : ℤ) := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.ARangeMemberIsCited.ARangeMemberIsCited
