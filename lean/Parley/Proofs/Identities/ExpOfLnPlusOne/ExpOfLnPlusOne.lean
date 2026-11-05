module

public import ComplexTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-of-ln-plus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpOfLnPlusOne.ExpOfLnPlusOne

theorem exp_of_ln_plus_one (x : ℝ) (hH2 : x > 0) :
    Real.exp (Real.log x + 1) = Real.exp 1 * x := by
  -- 1. mun:exp-sum a := ln(x), b := 1
  have s1 : Real.exp (Real.log x + 1) = Real.exp (Real.log x) * Real.exp (1 : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); parley_side)
  -- 2. substitute
  have s2 : Real.exp (Real.log x + 1) = x * Real.exp (1 : ℝ) := by
    have c1 : Real.exp (Real.log x) = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_side)
    have row1 : Real.exp (Real.log x + 1) = x * Real.exp (1 : ℝ) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : Real.exp (Real.log x + 1) = x * Real.exp 1 := by
    have c1 : Real.exp (1 : ℝ) = Real.exp 1 := by parley_real
    have row1 : Real.exp (Real.log x + 1) = x * Real.exp 1 := by parley_subst_at c1 s2
    exact row1
  -- 4. algebra, from 3
  have s4 : Real.exp (Real.log x + 1) = Real.exp 1 * x := by linear_combination (norm := parley_norm) s3
  all_goals exact s4

end Parley.Proofs.Identities.ExpOfLnPlusOne.ExpOfLnPlusOne
