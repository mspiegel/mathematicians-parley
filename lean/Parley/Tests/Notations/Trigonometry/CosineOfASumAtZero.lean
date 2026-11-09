module

public import ComplexTactics
public import NormTactics
public import PowerTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.CosineOfASumAtZero

theorem cosine_of_a_sum_at_zero :
    Real.cos (0 + 0 : ℝ) = 1 := by
  -- 1. thm:cos-add a := 0, b := 0
  have s1 : Real.cos (0 + 0 : ℝ) = Real.cos (0 : ℝ) * Real.cos (0 : ℝ) - Real.sin (0 : ℝ) * Real.sin (0 : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))) | exact_mod_cast ((Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ)))).symm | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); parley_int_power h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); parley_of_complex h) | (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); parley_side)
  -- 2. mun:cos-zero
  have s2 : Real.cos (0 : ℝ) = 1 := by exact Parley.Items.Stdlib.Trigonometry.mun_cos_zero
  -- 3. mun:sin-zero
  have s3 : Real.sin (0 : ℝ) = 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_sin_zero
  -- 4. substitute cos(0) = 1 (line 2) into line 1
  have s4 : Real.cos (0 + 0 : ℝ) = 1 * 1 - Real.sin (0 : ℝ) * Real.sin (0 : ℝ) := by parley_subst_at s2 s1
  -- 5. substitute sin(0) = 0 (line 3) into line 4
  have s5 : Real.cos (0 + 0 : ℝ) = 1 * 1 - 0 * 0 := by parley_subst_at s3 s4
  -- 6. calculation
  calc Real.cos (0 + 0 : ℝ) = 1 * 1 - 0 * 0 := by exact s5
    _ = 1 := by norm_num

end Parley.Tests.Notations.Trigonometry.CosineOfASumAtZero
