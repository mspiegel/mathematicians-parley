module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NatReal

theorem nat_real (m : ℕ) (hH1 : 0 < m) :
    True := by
  -- 1. mun:numbers-nat-real
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.NatReal
