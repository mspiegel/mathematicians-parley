module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsNegative

theorem abs_negative (x : ℝ) :
    abs (-x) = abs x := by
  -- 1. mun:numbers-abs-negative
  have s1 : abs (-x) = abs x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := x)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.AbsNegative
