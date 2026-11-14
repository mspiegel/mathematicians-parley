module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/cosine-plus-pi.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.CosinePlusPi.CosinePlusPi

theorem cosine_plus_pi (x : ℝ) :
    Real.cos (x + Real.pi) = -Real.cos x := by
  -- 1. calculation
  calc Real.cos (x + Real.pi) = Real.cos x * Real.cos Real.pi - Real.sin x * Real.sin Real.pi := by
        have hI : Real.cos (x + Real.pi) = Real.cos x * Real.cos Real.pi - Real.sin x * Real.sin Real.pi := by exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))))
        exact hI
    _ = Real.cos x * -1 - Real.sin x * Real.sin Real.pi := by
        have hv1 : Real.sin Real.pi = -(0) := by rw [congrArg Real.sin (show Real.pi = 0 + Real.pi by ring1), Real.sin_add_pi, Real.sin_zero]
        have hv2 : Real.cos Real.pi = -(1) := by rw [congrArg Real.cos (show Real.pi = 0 + Real.pi by ring1), Real.cos_add_pi, Real.cos_zero]
        linear_combination (Real.cos x) * hv2
    _ = Real.cos x * -1 - Real.sin x * 0 := by
        have hv1 : Real.sin Real.pi = -(0) := by rw [congrArg Real.sin (show Real.pi = 0 + Real.pi by ring1), Real.sin_add_pi, Real.sin_zero]
        linear_combination (-Real.sin x) * hv1
    _ = -Real.cos x := by ring1

end Parley.Proofs.Identities.CosinePlusPi.CosinePlusPi
