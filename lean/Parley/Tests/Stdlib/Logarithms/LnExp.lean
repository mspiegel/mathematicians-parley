module

public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnExp

theorem ln_exp (x : ℝ) :
    Real.log (Real.exp x) = x := by
  -- 1. mun:logarithms-ln-exp
  have s1 : Real.log (Real.exp x) = x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := x)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.LnExp
