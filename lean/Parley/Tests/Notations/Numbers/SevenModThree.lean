module

public import LeanBridges

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SevenModThree

theorem seven_mod_three :
    (7 : ℤ) % (3 : ℤ) = 1 := by
  -- 1. arithmetic
  have s1 : (7 : ℤ) % (3 : ℤ) = 1 := by parley_arith
  all_goals parley_side

end Parley.Tests.Notations.Numbers.SevenModThree
