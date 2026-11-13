module

public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-is-increasing.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpIsIncreasing.ExpIsIncreasing

theorem exp_is_increasing (a : ℝ) (b : ℝ) (hH3 : a < b) :
    Real.exp a < Real.exp b := by
  -- 1. mun:exp-positive x := a
  have s1 : Real.exp a > 0 := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := a))
  -- 2. mun:exp-positive x := b
  have s2 : Real.exp b > 0 := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := b))
  -- 3. calculation
  have s3 : Real.log (Real.exp a) < Real.log (Real.exp b) := by
    calc Real.log (Real.exp a) = a := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := a))
      _ < b := hH3
      _ = Real.log (Real.exp b) := by exact (Parley.Items.Stdlib.Logarithms.mun_ln_exp (x := b)).symm
  -- 4. mun:ln-order x := exp(a), y := exp(b), from 1, 2, 3
  exact ((Parley.Items.Stdlib.Logarithms.mun_ln_order (x := Real.exp a) (y := Real.exp b) s1 s2)).mpr s3

end Parley.Proofs.Identities.ExpIsIncreasing.ExpIsIncreasing
