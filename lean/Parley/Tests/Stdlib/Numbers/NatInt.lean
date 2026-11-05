module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.NatInt

theorem nat_int (m : ℕ) (hH1 : 0 < m) :
    True := by
  -- 1. mun:numbers-nat-int
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.NatInt
