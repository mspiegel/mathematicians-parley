module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.ExponentNegative

theorem exponent_negative (a : ℝ) (hH2 : a ≠ 0) (m : ℤ) :
    a ^ (-m) = 1 / a ^ m := by
  -- 1. mun:numbers-exponent-negative, from H2
  have s1 : a ^ (-m) = 1 / a ^ m := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_exponent_negative (a := a) (by parley_side) (m := m)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.ExponentNegative
