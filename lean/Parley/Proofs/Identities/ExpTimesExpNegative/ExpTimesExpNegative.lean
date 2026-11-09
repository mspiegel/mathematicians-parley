module

public import AlgebraTactics
public import InstanceTactics
public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from proofs/identities/exp-times-exp-negative.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.ExpTimesExpNegative.ExpTimesExpNegative

theorem exp_times_exp_negative (x : ℝ) :
    Real.exp x * Real.exp (-x) = 1 := by
  -- 1. algebra
  have s1 : x + -x = 0 := by parley_ring
  -- 2. calculation
  calc Real.exp x * Real.exp (-x) = Real.exp (x + -x) := by
        have hI : Real.exp (x + -x) = Real.exp x * Real.exp (-x) := by parley_instance_cast ((Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := (x : ℂ)) (b := -(x : ℂ))))
        exact hI.symm
    _ = Real.exp (0 : ℝ) := by (have h := congrArg (fun t : ℝ => Real.exp t) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 1 := by parley_real

end Parley.Proofs.Identities.ExpTimesExpNegative.ExpTimesExpNegative
