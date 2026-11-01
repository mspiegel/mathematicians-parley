module

public import Parley.Library

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.TwoToTheTenth

theorem two_to_the_tenth :
    (2 ^ 10 : ℤ) = 1024 := by
  -- 1. arithmetic
  have s1 : (2 ^ 10 : ℤ) = 1024 := by parley_arith
  all_goals parley_side

end Parley.Tests.Notations.Numbers.TwoToTheTenth
