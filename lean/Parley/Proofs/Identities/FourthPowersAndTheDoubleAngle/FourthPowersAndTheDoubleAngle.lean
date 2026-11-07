module

public import AlgebraTactics
public import ComplexTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/fourth-powers-and-the-double-angle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.FourthPowersAndTheDoubleAngle.FourthPowersAndTheDoubleAngle

theorem fourth_powers_and_the_double_angle (x : ℝ) :
    Real.cos x ^ 4 - Real.sin x ^ 4 = Real.cos (2 * x) := by
  -- 1. mun:sin-cos-squares a := x
  have s1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_side)
  -- 2. algebra
  have s2 : 2 * x = x + x := by parley_ring
  -- 3. calculation
  have s3 : Real.cos x ^ 4 - Real.sin x ^ 4 = Real.cos (2 * x) := by
    calc Real.cos x ^ 4 - Real.sin x ^ 4 = (Real.cos x ^ 2 - Real.sin x ^ 2) * (Real.sin x ^ 2 + Real.cos x ^ 2) := by parley_ring
      _ = (Real.cos x ^ 2 - Real.sin x ^ 2) * 1 := by parley_subst s1
      _ = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by parley_ring
      _ = Real.cos (x + x) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); parley_side)
      _ = Real.cos (2 * x) := by parley_subst s2
  all_goals exact s3

end Parley.Proofs.Identities.FourthPowersAndTheDoubleAngle.FourthPowersAndTheDoubleAngle
