module

public import LeanBridges

/-! Written from tests/elaborator/large-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.LargeArithmetic.RemainderOfAPower

theorem remainder_of_a_power :
    (10 ^ 3 : ℤ) % (7 : ℤ) = 6 := by
  -- 1. arithmetic
  have s1 : (10 ^ 3 : ℤ) % (7 : ℤ) = 6 := by parley_arith
  all_goals parley_side

end Parley.Tests.Elaborator.LargeArithmetic.RemainderOfAPower
