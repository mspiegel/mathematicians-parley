module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.TheOddOnesCounted

theorem the_odd_ones_counted :
    ({x ∈ ({(2 : ℤ), (3 : ℤ), (7 : ℤ), (8 : ℤ)} : Set ℤ) | Odd x}.ncard : ℤ) = 2 := by
  -- 1. inspection
  have s1 : ({x ∈ ({(2 : ℤ), (3 : ℤ), (7 : ℤ), (8 : ℤ)} : Set ℤ) | Odd x}.ncard : ℤ) = 2 := by parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.ListedNumerals.TheOddOnesCounted
