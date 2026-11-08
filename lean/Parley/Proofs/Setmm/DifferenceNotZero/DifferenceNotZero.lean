module

public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/setmm/difference-not-zero.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceNotZero.DifferenceNotZero

theorem difference_not_zero (A : ℝ) (B : ℝ) (hH3 : abs A < B) :
    B - A ≠ 0 := by
  -- 1. thm:abs-bounds x := A
  have s1a : A ≤ abs A := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1
  have s1b : -A ≤ abs A := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2
  -- 2. inequalities, from 1
  have s2 : A ≤ abs A := by parley_order
  -- 3. transitivity, from 2, H3
  have s3 : A < B := by parley_order
  -- 4. inequalities
  parley_side

end Parley.Proofs.Setmm.DifferenceNotZero.DifferenceNotZero
