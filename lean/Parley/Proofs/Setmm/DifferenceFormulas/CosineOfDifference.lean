module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/setmm/difference-formulas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceFormulas.CosineOfDifference

theorem cosine_of_difference (A : ℂ) (B : ℂ) :
    Complex.cos (A - B) = Complex.cos A * Complex.cos B + Complex.sin A * Complex.sin B := by
  -- 1. mun:cos-negative a := B
  have s1 : Complex.cos (-B) = Complex.cos B := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := B))
  -- 2. mun:sin-negative a := B
  have s2 : Complex.sin (-B) = -Complex.sin B := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := B))
  -- 3. algebra
  have s3 : A - B = A + -B := by parley_ring
  -- 4. calculation
  calc Complex.cos (A - B) = Complex.cos (A + -B) := by parley_subst s3
    _ = Complex.cos A * Complex.cos (-B) - Complex.sin A * Complex.sin (-B) := by exact (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := -B))
    _ = Complex.cos A * Complex.cos B - Complex.sin A * Complex.sin (-B) := by parley_subst s1
    _ = Complex.cos A * Complex.cos B - Complex.sin A * -Complex.sin B := by parley_subst s2
    _ = Complex.cos A * Complex.cos B + Complex.sin A * Complex.sin B := by parley_ring

end Parley.Proofs.Setmm.DifferenceFormulas.CosineOfDifference
