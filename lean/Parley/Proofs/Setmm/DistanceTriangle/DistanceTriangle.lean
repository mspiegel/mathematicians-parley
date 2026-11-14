module

public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/distance-triangle.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DistanceTriangle.DistanceTriangle

theorem distance_triangle (A : ℝ) (B : ℝ) (C : ℝ) :
    abs (A - B) ≤ abs (A - C) + abs (C - B) := by
  -- 1. thm:triangle-inequality a := A − C, b := C − B
  have s1 : abs (A - C + (C - B)) ≤ abs (A - C) + abs (C - B) := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - C) (b := C - B))
  -- 2. substitute
  have c1 : A - C + (C - B) = A - B := by ring1
  have row1 : abs (A - B) ≤ abs (A - C) + abs (C - B) := Eq.subst (motive := (fun t : ℝ => abs t ≤ abs (A - C) + abs (C - B))) c1 s1
  exact row1

end Parley.Proofs.Setmm.DistanceTriangle.DistanceTriangle
