module

public import AlgebraTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared

/-! Written from proofs/setmm/double-angle-cosine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DoubleAngleCosine.CosineOfDouble

theorem cosine_of_double (A : ℂ) :
    Complex.cos (2 * A) = 2 * Complex.cos A ^ 2 - 1 := by
  -- 1. thm:sine-squared-plus-cosine-squared
  have s1 : Complex.sin A ^ 2 + Complex.cos A ^ 2 = 1 := by first | linear_combination (norm := parley_norm) (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)) | (have h := (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)) | exact_mod_cast ((Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A))).symm | (have h := (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)); parley_int_power h) | (have h := (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A)); parley_side)
  -- 2. algebra
  have s2 : 2 * A = A + A := by parley_ring
  -- 3. calculation
  have s3 : Complex.cos (2 * A) = 2 * Complex.cos A ^ 2 - 1 := by
    calc Complex.cos (2 * A) = Complex.cos (A + A) := by parley_subst s2
      _ = Complex.cos A * Complex.cos A - Complex.sin A * Complex.sin A := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A)); parley_side)
      _ = 2 * Complex.cos A ^ 2 - 1 := by linear_combination (norm := parley_norm) (-1) * s1
  all_goals exact s3

end Parley.Proofs.Setmm.DoubleAngleCosine.CosineOfDouble
