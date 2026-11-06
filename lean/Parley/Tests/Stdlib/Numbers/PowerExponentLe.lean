module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerExponentLe

theorem power_exponent_le (c : ℝ) (j : ℤ) (hH2 : 0 ≤ j) (k : ℤ) (hH3 : 0 ≤ k) (hH4 : 1 ≤ c) (hH5 : j ≤ k) :
    c ^ j.toNat ≤ c ^ k.toNat := by
  -- 1. mun:numbers-power-exponent-le a := c, m := j, n := k, from H4, H5
  have s1 : c ^ j.toNat ≤ c ^ k.toNat := by first | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (by parley_side) (n := k) (by parley_side) (by parley_side) hH5); simp (disch := first | omega | positivity | nlinarith) only [parley_zpow_toNat] at h ⊢; first | exact_mod_cast h | linarith) | linarith [(Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (by parley_side) (n := k) (by parley_side) (by parley_side) hH5)] | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (by parley_side) (n := k) (by parley_side) (by parley_side) hH5); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (by parley_side) (n := k) (by parley_side) (by parley_side) hH5) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_exponent_le (a := c) (m := j) (by parley_side) (n := k) (by parley_side) (by parley_side) hH5); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerExponentLe
