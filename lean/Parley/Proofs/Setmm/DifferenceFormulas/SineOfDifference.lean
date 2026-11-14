module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
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
  have s3 : A - B = A + -B := by ring1
  -- 4. calculation
  calc Complex.sin (A - B) = Complex.sin (A + -B) := congrArg (fun t : ℂ => Complex.sin t) s3
    _ = Complex.sin A * Complex.cos (-B) + Complex.cos A * Complex.sin (-B) := by exact (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := -B))
    _ = Complex.sin A * Complex.cos B + Complex.cos A * Complex.sin (-B) := congrArg (fun t : ℂ => Complex.sin A * t + Complex.cos A * Complex.sin (-B)) s1
    _ = Complex.sin A * Complex.cos B + Complex.cos A * -Complex.sin B := congrArg (fun t : ℂ => Complex.sin A * Complex.cos B + Complex.cos A * t) s2
    _ = Complex.sin A * Complex.cos B - Complex.cos A * Complex.sin B := by ring1

end Parley.Proofs.Setmm.DifferenceFormulas.SineOfDifference
