module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfPower

theorem power_of_power (z : ℂ) (j : ℕ) (k : ℕ) :
    z ^ (j * k) = (z ^ j) ^ k := by
  -- 1. mun:numbers-power-of-power a := z, m := j, n := k
  have s1 : z ^ (j * k) = (z ^ j) ^ k := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_power (a := z) (m := j) (n := k)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerOfPower
