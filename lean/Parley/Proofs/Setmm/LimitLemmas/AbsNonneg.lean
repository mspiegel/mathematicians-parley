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

/-! Written from proofs/setmm/limit-lemmas.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.LimitLemmas.AbsNonneg

theorem abs_nonneg (x : ℝ) :
    abs x ≥ 0 := by
  -- 1. thm:abs-bounds
  have s1a : x ≤ abs x := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1
  have s1b : -x ≤ abs x := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2
  -- 2. inequalities, from 1
  have s2 : 0 ≤ 2 * abs x := by parley_order
  -- 3. inequalities
  have s3 : abs x ≥ 0 := by parley_order
  all_goals exact s3

end Parley.Proofs.Setmm.LimitLemmas.AbsNonneg
