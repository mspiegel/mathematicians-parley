module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from proofs/setmm/adding-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.AddingBounds.AddingBounds

theorem adding_bounds (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (hH5 : A ≤ C) (hH6 : B ≤ D) :
    A + B ≤ C + D := by
  -- 1. inequalities, from H5, H6
  linarith only [hH5, hH6]

end Parley.Proofs.Setmm.AddingBounds.AddingBounds
