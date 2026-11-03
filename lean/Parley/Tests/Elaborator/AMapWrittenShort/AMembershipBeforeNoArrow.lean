module

public import Tactics

/-! Written from tests/elaborator/a-map-written-short.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMapWrittenShort.AMembershipBeforeNoArrow

theorem a_membership_before_no_arrow (x : ℝ) (x : ℕ) (hH2 : 0 < x) :
    0 < x := by
  -- 1. restate H2
  have s1 : 0 < x := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.AMapWrittenShort.AMembershipBeforeNoArrow
