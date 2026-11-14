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

/-! Written from proofs/setmm/reverse-triangle-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow

theorem abs_difference_below (A : ℝ) (B : ℝ) :
    abs A - abs B ≤ abs (A - B) := by
  -- 1. thm:triangle-inequality a := A − B, b := B
  have s1 : abs (A - B + B) ≤ abs (A - B) + abs B := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))
  -- 2. substitute
  have s2 : abs A ≤ abs (A - B) + abs B := by
    have c1 : A - B + B = A := by ring1
    have row1 : abs A ≤ abs (A - B) + abs B := Eq.subst (motive := (fun t : ℝ => abs t ≤ abs (A - B) + abs B)) c1 s1
    exact row1
  -- 3. inequalities
  linarith only [s2]

end Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow
