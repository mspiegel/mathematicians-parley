module

public import AlgebraTactics
public import RealTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/setmm/double-angle-cosine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared

theorem sine_squared_plus_cosine_squared (A : ℂ) :
    Complex.sin A ^ 2 + Complex.cos A ^ 2 = 1 := by
  -- 1. mun:cos-negative a := A
  have s1 : Complex.cos (-A) = Complex.cos A := by exact (Parley.Items.Stdlib.Trigonometry.mun_cos_negative (a := A))
  -- 2. mun:sin-negative a := A
  have s2 : Complex.sin (-A) = -Complex.sin A := by exact (Parley.Items.Stdlib.Trigonometry.mun_sin_negative (a := A))
  -- 3. algebra
  have s3 : A + -A = 0 := by parley_ring
  -- 4. calculation
  calc Complex.sin A ^ 2 + Complex.cos A ^ 2 = Complex.cos A * Complex.cos A - Complex.sin A * -Complex.sin A := by parley_ring
    _ = Complex.cos A * Complex.cos A - Complex.sin A * Complex.sin (-A) := by parley_subst s2
    _ = Complex.cos A * Complex.cos (-A) - Complex.sin A * Complex.sin (-A) := by parley_subst s1
    _ = Complex.cos (A + -A) := (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := -A)).symm
    _ = (Real.cos (0 : ℝ) : ℂ) := by parley_subst s3
    _ = 1 := by parley_real

end Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared
