module

public import ComplexTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from tests/notations/trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Notations.Trigonometry.CosineOfASumAtZero

theorem cosine_of_a_sum_at_zero :
    Real.cos (0 + 0 : ℝ) = 1 := by
  -- 1. thm:cos-add a := 0, b := 0
  have s1 : Real.cos (0 + 0 : ℝ) = Real.cos (0 : ℝ) * Real.cos (0 : ℝ) - Real.sin (0 : ℝ) * Real.sin (0 : ℝ) := by (have h := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := (0 : ℂ)) (b := (0 : ℂ))); parley_of_complex h)
  -- 2. mun:cos-zero
  have s2 : Real.cos (0 : ℝ) = 1 := by exact Parley.Items.Stdlib.Trigonometry.mun_cos_zero
  -- 3. mun:sin-zero
  have s3 : Real.sin (0 : ℝ) = 0 := by exact Parley.Items.Stdlib.Trigonometry.mun_sin_zero
  -- 4. substitute cos(0) = 1 (line 2) into line 1
  have s4 : Real.cos (0 + 0 : ℝ) = 1 * 1 - Real.sin (0 : ℝ) * Real.sin (0 : ℝ) := by (have h := Eq.subst (motive := (fun t : ℝ => Real.cos (0 + 0 : ℝ) = t * t - Real.sin (0 : ℝ) * Real.sin (0 : ℝ))) s2 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 5. substitute sin(0) = 0 (line 3) into line 4
  have s5 : Real.cos (0 + 0 : ℝ) = 1 * 1 - 0 * 0 := by (have h := Eq.subst (motive := (fun t : ℝ => Real.cos (0 + 0 : ℝ) = 1 * 1 - t * t)) s3 s4; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. calculation
  calc Real.cos (0 + 0 : ℝ) = 1 * 1 - 0 * 0 := by exact s5
    _ = 1 := by norm_num

end Parley.Tests.Notations.Trigonometry.CosineOfASumAtZero
