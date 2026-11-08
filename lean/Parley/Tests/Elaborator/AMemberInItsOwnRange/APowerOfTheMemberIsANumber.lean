module

public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/a-member-in-its-own-range.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AMemberInItsOwnRange.APowerOfTheMemberIsANumber

theorem a_power_of_the_member_is_a_number (n : ℤ) (hH1 : 0 ≤ n) :
    True := by
  -- 1. membership
  exact trivial

end Parley.Tests.Elaborator.AMemberInItsOwnRange.APowerOfTheMemberIsANumber
