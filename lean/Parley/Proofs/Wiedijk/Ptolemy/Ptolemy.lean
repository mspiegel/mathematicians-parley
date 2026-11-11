module

public import AlgebraTactics
public import InstanceTactics
public import NormTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/wiedijk/ptolemy.proof by parley build lean. -/

public section

namespace Parley.Proofs.Wiedijk.Ptolemy.Ptolemy

theorem ptolemy (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) (hH5 : a + b + c + d = Real.pi) :
    Real.sin a * Real.sin b + Real.sin c * Real.sin d = Real.sin (b + c) * Real.sin (a + c) := by
  -- 1. algebra, from H5
  have s1 : d = Real.pi + -(a + b + c) := by linear_combination (norm := parley_norm) hH5
  -- 2. mun:sin-negative a := a + b + c
  have s2 : Real.sin (-(a + b + c)) = -Real.sin (a + b + c) := by
    have hI : Real.sin (-(a + b + c)) = -Real.sin (a + b + c) := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (a : ℂ) + (b : ℂ) + (c : ℂ))))
    exact hI
  -- 3. calculation
  have s3 : Real.sin d = Real.sin (a + b + c) := by
    calc Real.sin d = Real.sin (Real.pi + -(a + b + c)) := by (have h := congrArg (fun t : ℝ => Real.sin t) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = Real.sin Real.pi * Real.cos (-(a + b + c)) + Real.cos Real.pi * Real.sin (-(a + b + c)) := by
          have hI : Real.sin (Real.pi + -(a + b + c)) = Real.sin Real.pi * Real.cos (-(a + b + c)) + Real.cos Real.pi * Real.sin (-(a + b + c)) := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ)) (b := -((a : ℂ) + (b : ℂ) + (c : ℂ)))))
          exact hI
      _ = 0 * Real.cos (-(a + b + c)) + Real.cos Real.pi * Real.sin (-(a + b + c)) := by parley_real
      _ = 0 * Real.cos (-(a + b + c)) + -1 * Real.sin (-(a + b + c)) := by parley_real
      _ = 0 * Real.cos (-(a + b + c)) + -1 * -Real.sin (a + b + c) := by (have h := congrArg (fun t : ℝ => 0 * Real.cos (-(a + b + c)) + -1 * t) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
      _ = Real.sin (a + b + c) := by parley_ring
  -- 4. thm:sin-add a := a + b, b := c
  have s4 : Real.sin (a + b + c) = Real.sin (a + b) * Real.cos c + Real.cos (a + b) * Real.sin c := by
    have hI : Real.sin (a + b + c) = Real.sin (a + b) * Real.cos c + Real.cos (a + b) * Real.sin c := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (a : ℂ) + (b : ℂ)) (b := (c : ℂ))))
    exact hI
  -- 5. thm:sin-add
  have s5 : Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b := by
    have hI : Real.sin (a + b) = Real.sin a * Real.cos b + Real.cos a * Real.sin b := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (a : ℂ)) (b := (b : ℂ))))
    exact hI
  -- 6. thm:cos-add
  have s6 : Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b := by
    have hI : Real.cos (a + b) = Real.cos a * Real.cos b - Real.sin a * Real.sin b := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (a : ℂ)) (b := (b : ℂ))))
    exact hI
  -- 7. thm:sin-add a := b, b := c
  have s7 : Real.sin (b + c) = Real.sin b * Real.cos c + Real.cos b * Real.sin c := by
    have hI : Real.sin (b + c) = Real.sin b * Real.cos c + Real.cos b * Real.sin c := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (b : ℂ)) (b := (c : ℂ))))
    exact hI
  -- 8. thm:sin-add b := c
  have s8 : Real.sin (a + c) = Real.sin a * Real.cos c + Real.cos a * Real.sin c := by
    have hI : Real.sin (a + c) = Real.sin a * Real.cos c + Real.cos a * Real.sin c := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (a : ℂ)) (b := (c : ℂ))))
    exact hI
  -- 9. mun:sin-cos-squares a := c
  have s9 : Real.sin c ^ 2 + Real.cos c ^ 2 = 1 := by
    have hI : Real.sin c ^ 2 + Real.cos c ^ 2 = 1 := by parley_instance_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (c : ℂ))))
    exact hI
  -- 10. calculation
  calc Real.sin a * Real.sin b + Real.sin c * Real.sin d = Real.sin a * Real.sin b + Real.sin c * Real.sin (a + b + c) := by (have h := congrArg (fun t : ℝ => Real.sin a * Real.sin b + Real.sin c * t) s3; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.sin a * Real.sin b + Real.sin c * (Real.sin (a + b) * Real.cos c + Real.cos (a + b) * Real.sin c) := by (have h := congrArg (fun t : ℝ => Real.sin a * Real.sin b + Real.sin c * t) s4; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.sin a * Real.sin b + Real.sin c * ((Real.sin a * Real.cos b + Real.cos a * Real.sin b) * Real.cos c + Real.cos (a + b) * Real.sin c) := by (have h := congrArg (fun t : ℝ => Real.sin a * Real.sin b + Real.sin c * (t * Real.cos c + Real.cos (a + b) * Real.sin c)) s5; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.sin a * Real.sin b + Real.sin c * ((Real.sin a * Real.cos b + Real.cos a * Real.sin b) * Real.cos c + (Real.cos a * Real.cos b - Real.sin a * Real.sin b) * Real.sin c) := by (have h := congrArg (fun t : ℝ => Real.sin a * Real.sin b + Real.sin c * ((Real.sin a * Real.cos b + Real.cos a * Real.sin b) * Real.cos c + t * Real.sin c)) s6; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = (Real.sin b * Real.cos c + Real.cos b * Real.sin c) * (Real.sin a * Real.cos c + Real.cos a * Real.sin c) := by linear_combination (norm := parley_norm) (-(Real.sin a * Real.sin b)) * s9
    _ = Real.sin (b + c) * (Real.sin a * Real.cos c + Real.cos a * Real.sin c) := by (have h := congrArg (fun t : ℝ => t * (Real.sin a * Real.cos c + Real.cos a * Real.sin c)) s7.symm; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Real.sin (b + c) * Real.sin (a + c) := by (have h := congrArg (fun t : ℝ => Real.sin (b + c) * t) s8.symm; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Proofs.Wiedijk.Ptolemy.Ptolemy
