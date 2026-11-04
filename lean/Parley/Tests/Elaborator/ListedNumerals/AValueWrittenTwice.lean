module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.AValueWrittenTwice

theorem a_value_written_twice :
    (({(2 : ℤ), (3 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by
  -- 1. inspection
  have s1 : (({(2 : ℤ), (3 : ℤ), (2 : ℤ)} : Set ℤ).ncard : ℤ) = 2 := by parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.ListedNumerals.AValueWrittenTwice
