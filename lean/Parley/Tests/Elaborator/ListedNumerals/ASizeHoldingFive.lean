module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingFive

theorem a_size_holding_five :
    ({(1 : ℤ), (5 : ℤ), (9 : ℤ)} : Set ℤ).encard = ((3 : ℕ) : ℕ∞) := by
  -- 1. inspection
  have s1 : ({(1 : ℤ), (5 : ℤ), (9 : ℤ)} : Set ℤ).encard = ((3 : ℕ) : ℕ∞) := by parley_set_side
  all_goals exact s1

end Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingFive
