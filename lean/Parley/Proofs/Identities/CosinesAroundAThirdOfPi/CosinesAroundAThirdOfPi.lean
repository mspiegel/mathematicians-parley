module

public import InstanceTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Tactic.Ring.RingNF
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
  have s3 : Real.pi / 3 - x = Real.pi / 3 + -x := by ring1
  -- 4. mun:cos-negative a := x
  have s4 : Real.cos (-x) = Real.cos x := by
    have hI : Real.cos (-x) = Real.cos x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))))
    exact hI
  -- 5. mun:sin-negative a := x
  have s5 : Real.sin (-x) = -Real.sin x := by
    have hI : Real.sin (-x) = -Real.sin x := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))))
    exact hI
  -- 6. calculation
  calc Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 - x) = Real.cos (Real.pi / 3 + x) + Real.cos (Real.pi / 3 + -x) := congrArg (fun t : ℝ => Real.cos (Real.pi / 3 + x) + Real.cos t) s3
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + Real.cos (Real.pi / 3 + -x) := congrArg (fun t : ℝ => t + Real.cos (Real.pi / 3 + -x)) s1
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos (-x) - Real.sin (Real.pi / 3) * Real.sin (-x)) := congrArg (fun t : ℝ => Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + t) s2
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin (-x)) := congrArg (fun t : ℝ => Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * t - Real.sin (Real.pi / 3) * Real.sin (-x))) s4
    _ = Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * -Real.sin x) := congrArg (fun t : ℝ => Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * Real.sin x + (Real.cos (Real.pi / 3) * Real.cos x - Real.sin (Real.pi / 3) * t)) s5
    _ = 2 * Real.cos (Real.pi / 3) * Real.cos x := by ring_nf
    _ = 2 * (1 / 2) * Real.cos x := by
        have hv1 : Real.cos (Real.pi / 3) = 1 / 2 := by rw [congrArg Real.cos (show Real.pi / 3 = Real.pi / 3 by ring1), Real.cos_pi_div_three]
        linear_combination (2 * Real.cos x) * hv1
    _ = Real.cos x := by ring1

end Parley.Proofs.Identities.CosinesAroundAThirdOfPi.CosinesAroundAThirdOfPi
