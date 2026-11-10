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

/-! Written from proofs/identities/cosines-around-a-third-of-pi.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.CosinesAroundAThirdOfPi.CosinesAroundAThirdOfPi

theorem cosines_around_a_third_of_pi (x : ℝ) :
    Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 - x) = Real.cos x := by
  -- 1. thm:cos-add a := π/3, b := x
  have s1 : Real.cos (Real.pi / 3 + x) = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x := by
    have hI : Real.cos (Real.pi / 3 + x) = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := (x : ℂ))))
    exact hI
  -- 2. thm:cos-add a := π/3, b := −x
  have s2 : Real.cos (Real.pi / 3 + -x) = Real.cos (Real.pi / 3) * Real.cos (-x) - Real.sin (Real.pi / 3) * Real.sin (-x) := by
    have hI : Real.cos (Real.pi / 3 + -x) = Real.cos (Real.pi / 3) * Real.cos (-x) - Real.sin (Real.pi / 3) * Real.sin (-x) := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (Real.pi : ℂ) / 3) (b := -(x : ℂ))))
    exact hI
  -- 3. algebra
  have s3 : Real.pi / 3 - x = Real.pi / 3 + -x := by parley_ring
  -- 4. mun:cos-negative a := x
  have s4 : Real.cos (-x) = Real.cos x := by
    have hI : Real.cos (-x) = Real.cos x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))))
    exact hI
  -- 5. mun:sin-negative a := x
  have s5 : Real.sin (-x) = -Real.sin x := by
    have hI : Real.sin (-x) = -Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))))
    exact hI
  -- 6. calculation
  calc Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 - x) = Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 + -x) := by (have h := congrArg (fun t : ℝ => Real.cos (Real.pi / 3 + x) + Real.cos t) s3; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + Real.cos (Real.pi / 3 + -x) := by (have h := congrArg (fun t : ℝ => t + Real.cos (Real.pi / 3 + -x)) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos (-x) - Real.sin (Real.pi / 3) * Real.sin (-x)) := by (have h := congrArg (fun t : ℝ => Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + t) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin (-x)) := by (have h := congrArg (fun t : ℝ => Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * t - Real.sin (Real.pi / 3) * Real.sin (-x))) s4; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * -Real.sin x) := by (have h := congrArg (fun t : ℝ => Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * t)) s5; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = 2 * Real.cos (Real.pi / 3) * Real.cos x := by parley_ring
    _ = 2 * (1 / 2) * Real.cos x := by parley_real
    _ = Real.cos x := by parley_ring

end Parley.Proofs.Identities.CosinesAroundAThirdOfPi.CosinesAroundAThirdOfPi
