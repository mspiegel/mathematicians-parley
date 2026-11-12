module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
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
  have s2 : A ≤ abs A := by linarith only [s1a]
  -- 3. transitivity, from 2, H3
  have s3 : A < B := by exact lt_of_le_of_lt s2 hH3
  -- 4. inequalities
  exact ne_of_gt (by linarith only [s3])

end Parley.Proofs.Setmm.DifferenceNotZero.DifferenceNotZero
