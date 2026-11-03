module

public import Tactics

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.ThreeDividesTwelve

theorem three_divides_twelve :
    (3 : ℤ) ∣ (12 : ℤ) := by
  -- 1. arithmetic
  have s1 : (3 : ℤ) ∣ (12 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Divisibility.ThreeDividesTwelve
