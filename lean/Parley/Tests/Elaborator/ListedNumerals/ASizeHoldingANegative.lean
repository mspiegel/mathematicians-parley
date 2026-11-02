module

public import SetTactics
public import Tactics

/-! Written from tests/elaborator/listed-numerals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingANegative

theorem a_size_holding_a_negative :
    ({(-2 : ℤ), (0 : ℤ), (3 : ℤ)} : Set ℤ).encard = ((3 : ℕ) : ℕ∞) := by
  -- 1. inspection
  have s1 : ({(-2 : ℤ), (0 : ℤ), (3 : ℤ)} : Set ℤ).encard = ((3 : ℕ) : ℕ∞) := by parley_set_side
  all_goals parley_set_side

end Parley.Tests.Elaborator.ListedNumerals.ASizeHoldingANegative
