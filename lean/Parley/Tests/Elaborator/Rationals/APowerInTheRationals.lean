module

public import Tactics

/-! Written from tests/elaborator/rationals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Rationals.APowerInTheRationals

theorem a_power_in_the_rationals (a : ℕ) (hH1 : 0 < a) (b : ℕ) (c : ℤ) :
    True := by
  -- 1. membership
  all_goals parley_side

end Parley.Tests.Elaborator.Rationals.APowerInTheRationals
