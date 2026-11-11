module

public import ComplexTactics
public import NormTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-of-ln-plus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpOfLnPlusOne.ExpOfLnPlusOne

theorem exp_of_ln_plus_one (x : ℝ) (hH2 : x > 0) :
    Real.exp (Real.log x + 1) = Real.exp 1 * x := by
  -- 1. mun:exp-sum a := ln(x), b := 1
  have s1 : Real.exp (Real.log x + 1) = Real.exp (Real.log x) * Real.exp (1 : ℝ) := by (have h := (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (Real.log x : ℂ)) (b := (1 : ℂ))); parley_of_complex h)
  -- 2. substitute
  have s2 : Real.exp (Real.log x + 1) = x * Real.exp (1 : ℝ) := by
    have c1 : Real.exp (Real.log x) = x := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_ln (x := x) hH2)
    have row1 : Real.exp (Real.log x + 1) = x * Real.exp (1 : ℝ) := by parley_subst_at c1 s1
    exact row1
  -- 3. substitute
  have s3 : Real.exp (Real.log x + 1) = x * Real.exp 1 := by
    have c1 : Real.exp (1 : ℝ) = Real.exp 1 := by parley_real
    have row1 : Real.exp (Real.log x + 1) = x * Real.exp 1 := by parley_subst_at c1 s2
    exact row1
  -- 4. algebra, from 3
  linear_combination (norm := parley_norm) s3

end Parley.Proofs.Identities.ExpOfLnPlusOne.ExpOfLnPlusOne
