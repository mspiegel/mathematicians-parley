module

public import AlgebraTactics
public import InstanceTactics
public import RealTactics
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
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/cosine-plus-pi.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.CosinePlusPi.CosinePlusPi

theorem cosine_plus_pi (x : ℝ) :
    Real.cos (x + Real.pi) = -Real.cos x := by
  -- 1. calculation
  calc Real.cos (x + Real.pi) = Real.cos x * Real.cos Real.pi - Real.sin x * Real.sin Real.pi := by
        have hI : Real.cos (x + Real.pi) = Real.cos x * Real.cos Real.pi - Real.sin x * Real.sin Real.pi := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (Real.pi : ℂ))))
        exact hI
    _ = Real.cos x * -1 - Real.sin x * Real.sin Real.pi := by parley_real
    _ = Real.cos x * -1 - Real.sin x * 0 := by parley_real
    _ = -Real.cos x := by parley_ring

end Parley.Proofs.Identities.CosinePlusPi.CosinePlusPi
