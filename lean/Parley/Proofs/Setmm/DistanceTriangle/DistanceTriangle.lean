module

public import AlgebraTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/distance-triangle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DistanceTriangle.DistanceTriangle

theorem distance_triangle (A : ℝ) (B : ℝ) (C : ℝ) :
    abs (A - B) ≤ abs (A - C) + abs (C - B) := by
  -- 1. thm:triangle-inequality a := A − C, b := C − B
  have s1 : abs (A - C + (C - B)) ≤ abs (A - C) + abs (C - B) := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - C) (b := C - B))
  -- 2. substitute
  have c1 : A - C + (C - B) = A - B := by parley_ring
  have row1 : abs (A - B) ≤ abs (A - C) + abs (C - B) := by parley_subst_at c1 s1
  exact row1

end Parley.Proofs.Setmm.DistanceTriangle.DistanceTriangle
