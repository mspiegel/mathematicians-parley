module

public import PowerTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-is-increasing.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpIsIncreasing.ExpIsIncreasing

theorem exp_is_increasing (a : ℝ) (b : ℝ) (hH3 : a < b) :
    Real.exp a < Real.exp b := by
  -- 1. mun:exp-positive x := a
  have s1 : Real.exp a > 0 := by first | linarith [(Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := a))] | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := a)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := a)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := a)); parley_side)
  -- 2. mun:exp-positive x := b
  have s2 : Real.exp b > 0 := by first | linarith [(Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := b))] | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := b)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := b)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := b)); parley_side)
  -- 3. calculation
  have s3 : Real.log (Real.exp a) < Real.log (Real.exp b) := by
    calc Real.log (Real.exp a) = a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a)); parley_side)
      _ < b := by parley_side
      _ = Real.log (Real.exp b) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)); parley_side)
  -- 4. mun:ln-order x := exp(a), y := exp(b), from 1, 2, 3
  have s4 : Real.exp a < Real.exp b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := Real.exp a) (y := Real.exp b) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := Real.exp a) (y := Real.exp b) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals exact s4

end Parley.Proofs.Identities.ExpIsIncreasing.ExpIsIncreasing
