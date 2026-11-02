module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ExponentSumInteger

theorem exponent_sum_integer (a : ℝ) (hH2 : a ≠ 0) (m : ℤ) (n : ℤ) :
    a ^ (m + n) = a ^ m * a ^ n := by
  -- 1. mun:numbers-exponent-sum-integer, from H2
  have s1 : a ^ (m + n) = a ^ m * a ^ n := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_sum_integer (a := a) (by parley_side) (m := m) (n := n)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.ExponentSumInteger
