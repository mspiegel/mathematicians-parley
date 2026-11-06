module

public import ArithTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-root-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareRootByAlgebra.ASquareRootByAlgebra

theorem a_square_root_by_algebra (a : ℝ) :
    Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) * a = 2 * a := by
  -- 1. def:sqrt x := 2
  have r11_1 : (2 : ℤ) ≥ 0 := by parley_arith
  have s1a : Real.sqrt (2 : ℝ) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := (2 : ℝ)) (by parley_side)); parley_side)
  have s1b : Real.sqrt (2 : ℝ) ^ 2 = 2 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := (2 : ℝ)) (by parley_side)); parley_side)
  -- 2. algebra, from 1
  have s2 : Real.sqrt (2 : ℝ) * Real.sqrt (2 : ℝ) * a = 2 * a := by linear_combination (norm := parley_norm) (a) * s1b
  all_goals exact s2

end Parley.Tests.Elaborator.ASquareRootByAlgebra.ASquareRootByAlgebra
