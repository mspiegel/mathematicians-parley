module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerExponentLe

theorem power_exponent_le (c : ℝ) (j : ℕ) (k : ℕ) (hH4 : 1 ≤ c) (hH5 : (j : ℤ) ≤ (k : ℤ)) :
    c ^ j ≤ c ^ k := by
  -- 1. mun:numbers-power-exponent-le a := c, m := j, n := k, from H4, H5
  have s1 : c ^ j ≤ c ^ k := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (n := k) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (n := k) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (n := k) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (n := k) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerExponentLe
