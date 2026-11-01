module

public import Parley.Library

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SevenModThreeNotTwo

theorem seven_mod_three_not_two :
    (7 : ℤ) % (3 : ℤ) ≠ 2 := by
  -- 1. arithmetic
  have s1 : (7 : ℤ) % (3 : ℤ) ≠ 2 := by norm_num
  parley_side

end Parley.Tests.Notations.Numbers.SevenModThreeNotTwo
