module

public import AlgebraTactics
public import ComplexTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/setmm/difference-formulas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceFormulas.SineOfDifference

theorem sine_of_difference (A : ℂ) (B : ℂ) :
    Complex.sin (A - B) = Complex.sin A * Complex.cos B - Complex.cos A * Complex.sin B := by
  -- 1. mun:cos-negative a := B
  have s1 : Complex.cos (-B) = Complex.cos B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B)); parley_side)
  -- 2. mun:sin-negative a := B
  have s2 : Complex.sin (-B) = -Complex.sin B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B)); parley_side)
  -- 3. algebra
  have s3 : A - B = A + -B := by parley_ring
  -- 4. calculation
  have s4 : Complex.sin (A - B) = Complex.sin A * Complex.cos B - Complex.cos A * Complex.sin B := by
    calc Complex.sin (A - B) = Complex.sin (A + -B) := by parley_subst s3
      _ = Complex.sin A * Complex.cos (-B) + Complex.cos A * Complex.sin (-B) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B)); parley_side)
      _ = Complex.sin A * Complex.cos B + Complex.cos A * Complex.sin (-B) := by parley_subst s1
      _ = Complex.sin A * Complex.cos B + Complex.cos A * -Complex.sin B := by parley_subst s2
      _ = Complex.sin A * Complex.cos B - Complex.cos A * Complex.sin B := by parley_ring
  all_goals exact s4

end Parley.Proofs.Setmm.DifferenceFormulas.SineOfDifference
