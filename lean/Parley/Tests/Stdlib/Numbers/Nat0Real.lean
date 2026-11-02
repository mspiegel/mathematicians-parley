module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.Nat0Real

theorem nat0_real (m : ℕ) :
    True := by
  -- 1. mun:numbers-nat0-real
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.Nat0Real
