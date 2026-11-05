module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.PowerOfProductInteger

theorem power_of_product_integer (y : ℂ) (hH2 : y ≠ 0) (z : ℂ) (hH4 : z ≠ 0) (k : ℤ) :
    (y * z) ^ k = y ^ k * z ^ k := by
  -- 1. mun:numbers-power-of-product-integer a := y, b := z, n := k, from H2, H4
  have s1 : (y * z) ^ k = y ^ k * z ^ k := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_power_of_product_integer (a := y) (by parley_side) (b := z) (by parley_side) (n := k)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.PowerOfProductInteger
