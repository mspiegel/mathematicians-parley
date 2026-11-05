module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/powers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Powers.TheCubeOfACubeRoot

theorem the_cube_of_a_cube_root (x : ℂ) :
    (x ^ (1 / 3 : ℂ)) ^ 3 = x := by
  -- 1. mun:root-power n := 3
  have s1 : (x ^ (1 / 3 : ℂ)) ^ 3 = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_root_power (x := x) (n := 3) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Notations.Powers.TheCubeOfACubeRoot
