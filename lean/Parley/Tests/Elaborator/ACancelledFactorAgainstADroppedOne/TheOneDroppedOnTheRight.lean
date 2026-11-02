module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-cancelled-factor-against-a-dropped-one.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheRight

theorem the_one_dropped_on_the_right (x : ℝ) (k : ℝ) (hH3 : x ≠ 0) (hH4 : 2 * k * x = x) :
    2 * k = 1 := by
  -- 1. mun:multiply-cancel a := 2·k, b := 1, c := x, from H3, H4
  have s1 : 2 * k = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := 2 * k) (b := (1 : ℝ)) (c := x) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Elaborator.ACancelledFactorAgainstADroppedOne.TheOneDroppedOnTheRight
