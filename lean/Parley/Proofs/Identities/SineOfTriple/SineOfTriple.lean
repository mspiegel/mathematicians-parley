module

public import AlgebraTactics
public import ComplexTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/identities/sine-of-triple.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SineOfTriple.SineOfTriple

theorem sine_of_triple (x : ℝ) :
    Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by
  -- 1. algebra
  have s1 : 2 * x = x + x := by parley_ring
  -- 2. calculation
  have s2 : Real.sin (2 * x) = Real.sin x * Real.cos x + Real.cos x * Real.sin x := by
    calc Real.sin (2 * x) = Real.sin (x + x) := by parley_subst s1
      _ = Real.sin x * Real.cos x + Real.cos x * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := (x : ℂ)) (b := (x : ℂ))); parley_side)
  -- 3. calculation
  have s3 : Real.cos (2 * x) = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by
    calc Real.cos (2 * x) = Real.cos (x + x) := by parley_subst s1
      _ = Real.cos x * Real.cos x - Real.sin x * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (x : ℂ)) (b := (x : ℂ))); parley_side)
  -- 4. algebra
  have s4 : 3 * x = 2 * x + x := by parley_ring
  -- 5. mun:sin-cos-squares a := x
  have s5 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_cos_squares (a := (x : ℂ))); parley_side)
  -- 6. calculation
  have s6 : Real.sin (3 * x) = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by
    calc Real.sin (3 * x) = Real.sin (2 * x + x) := by parley_subst s4
      _ = Real.sin (2 * x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := 2 * (x : ℂ)) (b := (x : ℂ))); parley_side)
      _ = (Real.sin x * Real.cos x + Real.cos x * Real.sin x) * Real.cos x + Real.cos (2 * x) * Real.sin x := by parley_subst s2
      _ = (Real.sin x * Real.cos x + Real.cos x * Real.sin x) * Real.cos x + (Real.cos x * Real.cos x - Real.sin x * Real.sin x) * Real.sin x := by parley_subst s3
      _ = 3 * Real.sin x - 4 * Real.sin x ^ 3 := by linear_combination (norm := parley_norm) (3 * Real.sin x) * s5
  all_goals exact s6

end Parley.Proofs.Identities.SineOfTriple.SineOfTriple
