module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.BoundedByItsSize

theorem bounded_by_its_size (x : ℝ) :
    x ≤ abs x ∧ -x ≤ abs x := by
  -- 1. thm:abs-sum
  have s1a : x ≤ abs x := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1
  have s1b : -x ≤ abs x := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2
  exact ⟨s1a, s1b⟩

end Parley.Tests.Docs.Grammar.BoundedByItsSize
