module

public import ComplexTactics
public import PowerTactics
public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpLn

theorem exp_ln (x : ℝ) (hH2 : x > 0) :
    Real.exp (Real.log x) = x := by
  -- 1. mun:logarithms-exp-ln, from H2
  have s1 : Real.exp (Real.log x) = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.ExpLn
