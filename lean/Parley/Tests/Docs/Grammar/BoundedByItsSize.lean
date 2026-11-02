module

public import Tactics
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from tests/docs/grammar.proof by parley build lean. -/

public section

namespace Parley.Tests.Docs.Grammar.BoundedByItsSize

theorem bounded_by_its_size (x : ℝ) :
    x ≤ abs x ∧ -x ≤ abs x := by
  -- 1. thm:abs-sum
  have s1a : x ≤ abs x := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).1; parley_side)
  have s1b : -x ≤ abs x := by first | linarith [(Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2] | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2; push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2 | (have h := (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := x)).2; parley_side)
  exact ⟨by parley_side, by parley_side⟩

end Parley.Tests.Docs.Grammar.BoundedByItsSize
