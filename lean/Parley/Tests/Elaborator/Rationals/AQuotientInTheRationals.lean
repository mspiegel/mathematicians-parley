module

public import Tactics
public import Mathlib.Data.Int.Notation

/-! Written from tests/elaborator/rationals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.Rationals.AQuotientInTheRationals

theorem a_quotient_in_the_rationals (a : ℤ) (hH1 : 0 < a) (f : ℤ → ℤ) :
    True := by
  -- 1. membership, from H2
  all_goals parley_side

end Parley.Tests.Elaborator.Rationals.AQuotientInTheRationals
