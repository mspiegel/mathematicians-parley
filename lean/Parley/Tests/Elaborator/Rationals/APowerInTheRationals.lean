module

public import Parley.Library

/-! Written from tests/elaborator/rationals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Rationals.APowerInTheRationals

theorem a_power_in_the_rationals (a : ℕ) (H1 : 0 < a) (b : ℕ) (c : ℤ) :
    True := by
  -- 1. membership
  parley_side

end Parley.Tests.Elaborator.Rationals.APowerInTheRationals
