module

public import AlgebraTactics
public import ComplexTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/sine-of-half-pi-minus.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SineOfHalfPiMinus.SineOfHalfPiMinus

theorem sine_of_half_pi_minus (x : ℝ) :
    Real.sin (Real.pi / 2 - x) = Real.cos x := by
  -- 1. algebra
  have s1 : Real.pi / 2 - x = Real.pi / 2 + -x := by parley_ring
  -- 2. mun:cos-negative a := x
  have s2 : Real.cos (-x) = Real.cos x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := (x : ℂ))); parley_side)
  -- 3. mun:sin-negative a := x
  have s3 : Real.sin (-x) = -Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := (x : ℂ))); parley_side)
  -- 4. calculation
  have s4 : Real.sin (Real.pi / 2 - x) = Real.cos x := by
    calc Real.sin (Real.pi / 2 - x) = Real.sin (Real.pi / 2 + -x) := by parley_subst s1
      _ = Real.sin (Real.pi / 2) * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (Real.pi : ℂ) / 2) (b := -(x : ℂ))); parley_side)
      _ = 1 * Real.cos (-x) + Real.cos (Real.pi / 2) * Real.sin (-x) := by parley_real
      _ = 1 * Real.cos (-x) + 0 * Real.sin (-x) := by parley_real
      _ = 1 * Real.cos x + 0 * Real.sin (-x) := by parley_subst s2
      _ = 1 * Real.cos x + 0 * -Real.sin x := by parley_subst s3
      _ = Real.cos x := by parley_ring
  all_goals exact s4

end Parley.Proofs.Identities.SineOfHalfPiMinus.SineOfHalfPiMinus
