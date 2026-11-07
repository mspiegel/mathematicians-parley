module

public import NormTactics
public import PowerTactics
public import SubstTactics
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

/-! Written from proofs/hammack/ln-is-injective.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.LnIsInjective.LnIsInjective

theorem ln_is_injective (x : ℝ) (y : ℝ) (hH3 : x > 0) (hH4 : y > 0) (hH5 : Real.log x = Real.log y) :
    x = y := by
  -- 1. calculation
  have s1 : x = y := by
    calc x = Real.exp (Real.log x) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) (by parley_side)); parley_side)
      _ = Real.exp (Real.log y) := by parley_subst hH5
      _ = y := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := y) (by parley_side))
  all_goals exact s1

end Parley.Proofs.Hammack.LnIsInjective.LnIsInjective
