module

public import LeanBridges

/-! Written from tests/elaborator/a-member-in-its-own-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMemberInItsOwnRange.AMemberIsANumber

theorem a_member_is_a_number (n : ℕ) (hH1 : 0 < n) :
    True := by
  -- 1. membership
  all_goals parley_side

end Parley.Tests.Elaborator.AMemberInItsOwnRange.AMemberIsANumber
