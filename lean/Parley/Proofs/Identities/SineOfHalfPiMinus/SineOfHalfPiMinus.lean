module

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

/-! Written from proofs/identities/sine-of-half-pi-minus.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SineOfHalfPiMinus.SineOfHalfPiMinus

theorem sine_of_half_pi_minus (x : ℝ) :
    Real.sin (Real.pi / 2 - x) = Real.cos x := by
  -- 1. algebra
  have s1 : Real.pi / 2 - x = Real.pi / 2 + -x := by ring1
  -- 2. mun:cos-negative a := x
  have s2 : Real.cos (-x) = Real.cos x := by
    have hI : Real.cos (-x) = Real.cos x := by exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))))
    exact hI
  -- 3. mun:sin-negative a := x
  have s3 : Real.sin (-x) = -Real.sin x := by
    have hI : Real.sin (-x) = -Real.sin x := by exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))))
    exact hI
  -- 4. calculation
  calc Real.sin (Real.pi / 2 - x) = Real.sin (Real.pi / 2 + -x) := congrArg (fun t : ℝ => Real.sin t) s1
    _ = Real.sin (Real.pi / 2) * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by
        have hI : Real.sin (Real.pi / 2 + -x) = Real.sin (Real.pi / 2) * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))))
        exact hI
    _ = 1 * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by
        have hv1 : Real.cos (Real.pi / 2) = -(0) := by rw [congrArg Real.cos (show Real.pi / 2 = 0 + Real.pi / 2 by ring1), Real.cos_add_pi_div_two, Real.sin_zero]
        have hv2 : Real.sin (Real.pi / 2) = 1 := by rw [congrArg Real.sin (show Real.pi / 2 = 0 + Real.pi / 2 by ring1), Real.sin_add_pi_div_two, Real.cos_zero]
        linear_combination (Real.cos (-x)) * hv2
    _ = 1 * Real.cos (-x) + 0 * Real.sin (-x) := by
        have hv1 : Real.cos (Real.pi / 2) = -(0) := by rw [congrArg Real.cos (show Real.pi / 2 = 0 + Real.pi / 2 by ring1), Real.cos_add_pi_div_two, Real.sin_zero]
        linear_combination (Real.sin (-x)) * hv1
    _ = 1 * Real.cos x + 0 * Real.sin (-x) := congrArg (fun t : ℝ => 1 * t + 0 * Real.sin (-x)) s2
    _ = 1 * Real.cos x + 0 * -Real.sin x := congrArg (fun t : ℝ => 1 * Real.cos x + 0 * t) s3
    _ = Real.cos x := by ring_nf

end Parley.Proofs.Identities.SineOfHalfPiMinus.SineOfHalfPiMinus
