module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.ARealPowerOfAPositiveReal

theorem a_real_power_of_a_positive_real (x : ℝ) (hH2 : x > 0) (y : ℝ) :
    x ^ y > 0 := by
  -- 1. mun:real-power-positive, from H2
  have s1 : x ^ y > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := x) (by parley_side) (y := y))] | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := x) (by parley_side) (y := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := x) (by parley_side) (y := y)) | (have h := (Parley.Items.Stdlib.Numbers.mun_real_power_positive (x := x) (by parley_side) (y := y)); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Powers.ARealPowerOfAPositiveReal
