module

public import Parley.Library

/-! Written from tests/elaborator/a-member-in-its-own-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMemberInItsOwnRange.ATermOfTheMemberIsANumber

theorem a_term_of_the_member_is_a_number (n : ℕ) (H1 : 0 < n) :
    True := by
  -- 1. membership
  all_goals parley_side

end Parley.Tests.Elaborator.AMemberInItsOwnRange.ATermOfTheMemberIsANumber
