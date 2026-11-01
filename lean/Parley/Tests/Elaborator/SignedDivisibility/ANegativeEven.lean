module

public import Parley.Library

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeEven

theorem a_negative_even :
    Even (-6 : ℤ) := by
  -- 1. arithmetic
  have s1 : Even (-6 : ℤ) := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeEven
