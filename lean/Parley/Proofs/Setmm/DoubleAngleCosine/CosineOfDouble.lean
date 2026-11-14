module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Trigonometry
public import Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared

/-! Written from proofs/setmm/double-angle-cosine.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DoubleAngleCosine.CosineOfDouble

theorem cosine_of_double (A : ℂ) :
    Complex.cos (2 * A) = 2 * Complex.cos A ^ 2 - 1 := by
  -- 1. thm:sine-squared-plus-cosine-squared
  have s1 : Complex.sin A ^ 2 + Complex.cos A ^ 2 = 1 := by exact (Parley.Proofs.Setmm.DoubleAngleCosine.SineSquaredPlusCosineSquared.sine_squared_plus_cosine_squared (A := A))
  -- 2. algebra
  have s2 : 2 * A = A + A := by ring1
  -- 3. calculation
  calc Complex.cos (2 * A) = Complex.cos (A + A) := congrArg (fun t : ℂ => Complex.cos t) s2
    _ = Complex.cos A * Complex.cos A - Complex.sin A * Complex.sin A := by exact (Parley.Items.Stdlib.Trigonometry.thm_cos_add (a := A) (b := A))
    _ = 2 * Complex.cos A ^ 2 - 1 := by linear_combination (-1) * s1

end Parley.Proofs.Setmm.DoubleAngleCosine.CosineOfDouble
