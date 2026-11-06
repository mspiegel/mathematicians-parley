module

public import Tactics

/-! Written from tests/elaborator/a-member-in-its-own-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMemberInItsOwnRange.AMemberNamedI

theorem a_member_named_i (n : ℤ) (hH1 : 0 ≤ n) :
    True := by
  -- 1. membership
  all_goals parley_side

end Parley.Tests.Elaborator.AMemberInItsOwnRange.AMemberNamedI
