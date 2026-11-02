module

public import Tactics

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.TheOddOnesOfASignedList

theorem the_odd_ones_of_a_signed_list :
    {x ∈ ({(-3 : ℤ), (-2 : ℤ), (0 : ℤ), (5 : ℤ)} : Set ℤ) | Odd x} = ({(-3 : ℤ), (5 : ℤ)} : Set ℤ) := by
  -- 1. inspection
  have s1 : {x ∈ ({(-3 : ℤ), (-2 : ℤ), (0 : ℤ), (5 : ℤ)} : Set ℤ) | Odd x} = ({(-3 : ℤ), (5 : ℤ)} : Set ℤ) := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.SignedDivisibility.TheOddOnesOfASignedList
