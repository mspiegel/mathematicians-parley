module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0Int

theorem nat0_int (m : ℕ) :
    True := by
  -- 1. mun:numbers-nat0-int
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.Nat0Int
