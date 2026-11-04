module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.OnePower

theorem one_power (m : ℤ) :
    (1 ^ m : ℚ) = 1 := by
  -- 1. mun:numbers-one-power
  have s1 : (1 ^ m : ℚ) = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_one_power (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_one_power (m := m)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.OnePower
