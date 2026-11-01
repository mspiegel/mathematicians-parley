module

public import Parley.Library

/-! Written from tests/elaborator/rationals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Rationals.AValueInTheRationals

theorem a_value_in_the_rationals (a : ℕ) (hH1 : 0 < a) (f : ℕ → ℤ) :
    True := by
  -- 1. membership, from H2
  all_goals parley_side

end Parley.Tests.Elaborator.Rationals.AValueInTheRationals
