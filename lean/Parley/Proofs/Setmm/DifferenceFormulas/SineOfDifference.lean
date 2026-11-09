module

public import AlgebraTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/setmm/difference-formulas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceFormulas.SineOfDifference

theorem sine_of_difference (A : ℂ) (B : ℂ) :
    Complex.sin (A - B) = Complex.sin A * Complex.cos B - Complex.cos A * Complex.sin B := by
  -- 1. mun:cos-negative a := B
  have s1 : Complex.cos (-B) = Complex.cos B := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B))
  -- 2. mun:sin-negative a := B
  have s2 : Complex.sin (-B) = -Complex.sin B := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B))
  -- 3. algebra
  have s3 : A - B = A + -B := by parley_ring
  -- 4. calculation
  calc Complex.sin (A - B) = Complex.sin (A + -B) := by (have h := congrArg (fun t : ℂ => Complex.sin t) s3; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Complex.sin A * Complex.cos (-B) + Complex.cos A * Complex.sin (-B) := by exact (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B))
    _ = Complex.sin A * Complex.cos B + Complex.cos A * Complex.sin (-B) := by (have h := congrArg (fun t : ℂ => Complex.sin A * t + Complex.cos A * Complex.sin (-B)) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Complex.sin A * Complex.cos B + Complex.cos A * -Complex.sin B := by (have h := congrArg (fun t : ℂ => Complex.sin A * Complex.cos B + Complex.cos A * t) s2; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Complex.sin A * Complex.cos B - Complex.cos A * Complex.sin B := by parley_ring

end Parley.Proofs.Setmm.DifferenceFormulas.SineOfDifference
