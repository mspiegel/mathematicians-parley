module

public import AlgebraTactics
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
public import Parley.Items.Stdlib.Trigonometry

/-! Written from proofs/setmm/sine-of-double.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.SineOfDouble.SineOfDouble

theorem sine_of_double (A : ℂ) :
    Complex.sin (2 * A) = 2 * Complex.sin A * Complex.cos A := by
  -- 1. algebra
  have s1 : 2 * A = A + A := by parley_ring
  -- 2. calculation
  calc Complex.sin (2 * A) = Complex.sin (A + A) := by (have h := congrArg (fun t : ℂ => Complex.sin t) s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    _ = Complex.sin A * Complex.cos A + Complex.cos A * Complex.sin A := by exact (Parley.Items.Stdlib.Trigonometry.thm_sin_add (a := A) (b := A))
    _ = 2 * Complex.sin A * Complex.cos A := by parley_ring

end Parley.Proofs.Setmm.SineOfDouble.SineOfDouble
