module

public import Tactics

/-! Written from tests/notations/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Divisibility.ZeroIsEven

theorem zero_is_even :
    Even (0 : ℤ) := by
  -- 1. arithmetic
  have s1 : Even (0 : ℤ) := by parley_arith
  all_goals exact s1

end Parley.Tests.Notations.Divisibility.ZeroIsEven
