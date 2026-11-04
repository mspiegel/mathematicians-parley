module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsPower

theorem abs_power (x : ℝ) (n : ℕ) :
    abs (x ^ n) = abs x ^ n := by
  -- 1. mun:numbers-abs-power
  have s1 : abs (x ^ n) = abs x ^ n := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_power (x := x) (n := n)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsPower
