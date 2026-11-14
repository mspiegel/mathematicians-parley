module

public import InstanceTactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-times-exp-negative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpTimesExpNegative.ExpTimesExpNegative

theorem exp_times_exp_negative (x : ℝ) :
    Real.exp x * Real.exp (-x) = 1 := by
  -- 1. algebra
  have s1 : x + -x = 0 := by ring1
  -- 2. calculation
  calc Real.exp x * Real.exp (-x) = Real.exp (x + -x) := by
        have hI : Real.exp (x + -x) = Real.exp x * Real.exp (-x) := by parley_instance_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))))
        exact hI.symm
    _ = Real.exp (0 : ℝ) := by (have h := congrArg (fun t : ℝ => Real.exp t) s1; push_cast at h ⊢; exact_mod_cast h)
    _ = 1 := by
        have hv1 : Real.exp (0 : ℝ) = 1 := by rw [Real.exp_zero]
        linear_combination hv1

end Parley.Proofs.Identities.ExpTimesExpNegative.ExpTimesExpNegative
