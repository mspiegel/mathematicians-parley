module

public import AlgebraTactics
public import InstanceTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/sine-of-half-pi-minus.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SineOfHalfPiMinus.SineOfHalfPiMinus

theorem sine_of_half_pi_minus (x : ℝ) :
    Real.sin (Real.pi / 2 - x) = Real.cos x := by
  -- 1. algebra
  have s1 : Real.pi / 2 - x = Real.pi / 2 + -x := by parley_ring
  -- 2. mun:cos-negative a := x
  have s2 : Real.cos (-x) = Real.cos x := by
    have hI : Real.cos (-x) = Real.cos x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))))
    exact hI
  -- 3. mun:sin-negative a := x
  have s3 : Real.sin (-x) = -Real.sin x := by
    have hI : Real.sin (-x) = -Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))))
    exact hI
  -- 4. calculation
  calc Real.sin (Real.pi / 2 - x) = Real.sin (Real.pi / 2 + -x) := by (have h := congrArg (fun t : ℝ => Real.sin t) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.sin (Real.pi / 2) * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by
        have hI : Real.sin (Real.pi / 2 + -x) = Real.sin (Real.pi / 2) * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))))
        exact hI
    _ = 1 * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by parley_real
    _ = 1 * Real.cos (-x) + 0 * Real.sin (-x) := by parley_real
    _ = 1 * Real.cos x + 0 * Real.sin (-x) := by (have h := congrArg (fun t : ℝ => 1 * t + 0 * Real.sin (-x)) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 1 * Real.cos x + 0 * -Real.sin x := by (have h := congrArg (fun t : ℝ => 1 * Real.cos x + 0 * t) s3; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.cos x := by parley_ring

end Parley.Proofs.Identities.SineOfHalfPiMinus.SineOfHalfPiMinus
