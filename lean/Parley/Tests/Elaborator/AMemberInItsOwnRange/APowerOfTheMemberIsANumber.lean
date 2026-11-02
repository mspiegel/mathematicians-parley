module

public import LeanBridges

/-! Written from tests/elaborator/a-member-in-its-own-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMemberInItsOwnRange.APowerOfTheMemberIsANumber

theorem a_power_of_the_member_is_a_number (n : ℕ) :
    True := by
  -- 1. membership
  all_goals parley_side

end Parley.Tests.Elaborator.AMemberInItsOwnRange.APowerOfTheMemberIsANumber
