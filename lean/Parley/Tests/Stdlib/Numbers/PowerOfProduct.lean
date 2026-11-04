module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfProduct

theorem power_of_product (y : ℂ) (z : ℂ) (k : ℕ) :
    (y * z) ^ k = y ^ k * z ^ k := by
  -- 1. mun:numbers-power-of-product a := y, b := z, n := k
  have s1 : (y * z) ^ k = y ^ k * z ^ k := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product (a := y) (b := z) (n := k)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerOfProduct
