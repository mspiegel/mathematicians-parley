module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/notations/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Numbers.SqrtFour

theorem sqrt_four :
    Real.sqrt (4 : ℝ) = 2 := by
  -- 1. def:sqrt x := 4
  have r88_1 : (4 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (4 : ℝ) ^ 2 = 4 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (4 : ℝ)) (by parley_side)); parley_side)
  have s1b : Real.sqrt (4 : ℝ) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (4 : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (4 : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (4 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (4 : ℝ)) (by parley_side)); parley_side)
  -- 2. calculation
  have s2 : Real.sqrt (4 : ℝ) ^ 2 = 2 ^ 2 := by
    calc Real.sqrt (4 : ℝ) ^ 2 = 4 := by parley_side
      _ = 2 ^ 2 := by norm_num
  -- 3. mun:square-equal x := √4, y := 2, from 2
  have r97_1 : Real.sqrt (4 : ℝ) ≥ 0 := by parley_side
  have r97_2 : (2 : ℤ) ≥ 0 := by parley_arith
  have s3 : Real.sqrt (4 : ℝ) = 2 := by first | linear_combination (norm := parley_norm) ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side) | exact_mod_cast (((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side)).symm | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); rify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); qify; linear_combination (norm := parley_norm) h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); parley_int_power h) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_equal (x := Real.sqrt (4 : ℝ)) (y := (2 : ℝ)) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
  all_goals exact s3

end Parley.Tests.Notations.Numbers.SqrtFour
