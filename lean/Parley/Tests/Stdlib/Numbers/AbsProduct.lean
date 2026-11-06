module

public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.AbsProduct

theorem abs_product (x : ℝ) (y : ℝ) :
    abs (x * y) = abs x * abs y := by
  -- 1. mun:numbers-abs-product
  have s1 : abs (x * y) = abs x * abs y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_abs_product (x := x) (y := y)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.AbsProduct
