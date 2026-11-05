module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerRealInteger

theorem power_real_integer (x : ℝ) (hH2 : x ≠ 0) (k : ℤ) :
    True := by
  -- 1. mun:numbers-power-real-integer a := x, m := k − 1, from H2
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.PowerRealInteger
