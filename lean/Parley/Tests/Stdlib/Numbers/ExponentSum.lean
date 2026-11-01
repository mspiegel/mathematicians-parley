module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ExponentSum

theorem exponent_sum (a : ℝ) (m : ℕ) (n : ℕ) :
    a ^ (m + n) = a ^ m * a ^ n := by
  -- 1. mun:numbers-exponent-sum
  have s1 : a ^ (m + n) = a ^ m * a ^ n := by linear_combination (Parley.Items.Stdlib.Numbers.mun_exponent_sum (a := a) (m := m) (n := n))
  parley_side

end Parley.Tests.Stdlib.Numbers.ExponentSum
