module

public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnProduct

theorem ln_product (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) :
    Real.log (x * y) = Real.log x + Real.log y := by
  -- 1. mun:logarithms-ln-product, from H3, H4
  have s1 : Real.log (x * y) = Real.log x + Real.log y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_product (x := x) (y := y) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnProduct
