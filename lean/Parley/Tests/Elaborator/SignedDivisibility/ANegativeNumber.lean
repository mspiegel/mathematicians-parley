module

public import Parley.Library

/-! Written from tests/elaborator/signed-divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber

theorem a_negative_number :
    (2 : ℤ) ∣ (-8 : ℤ) := by
  -- 1. arithmetic
  have s1 : (2 : ℤ) ∣ (-8 : ℤ) := by norm_num
  parley_side

end Parley.Tests.Elaborator.SignedDivisibility.ANegativeNumber
