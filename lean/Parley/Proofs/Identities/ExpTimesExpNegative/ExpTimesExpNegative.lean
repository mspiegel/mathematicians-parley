module

public import AlgebraTactics
public import ComplexTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-times-exp-negative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpTimesExpNegative.ExpTimesExpNegative

theorem exp_times_exp_negative (x : ℝ) :
    Real.exp x * Real.exp (-x) = 1 := by
  -- 1. algebra
  have s1 : x + -x = 0 := by parley_ring
  -- 2. calculation
  have s2 : Real.exp x * Real.exp (-x) = 1 := by
    calc Real.exp x * Real.exp (-x) = Real.exp (x + -x) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))); parley_side)
      _ = Real.exp (0 : ℝ) := by parley_subst s1
      _ = 1 := by parley_real
  all_goals exact s2

end Parley.Proofs.Identities.ExpTimesExpNegative.ExpTimesExpNegative
