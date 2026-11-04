module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/an-interval-member-is-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberInAMethod

theorem an_interval_member_in_a_method (s : ℝ) (hH1 : s ∈ (Set.Icc (0 : ℝ) (1 : ℝ) : Set ℝ)) (t : ℝ) (hH2 : t ∈ (Set.Ioo (0 : ℝ) (1 : ℝ) : Set ℝ)) :
    True := by
  -- 1. membership
  all_goals parley_set_side

end Parley.Tests.Elaborator.AnIntervalMemberIsCited.AnIntervalMemberInAMethod
