module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/difference-of-sizes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceOfSizes.DifferenceOfSizes

theorem difference_of_sizes (A : ℝ) (B : ℝ) :
    abs A - abs B ≤ abs (A - B) := by
  -- 1. thm:triangle-inequality a := A − B, b := B
  have s1 : abs (A - B + B) ≤ abs (A - B) + abs B := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))
  -- 2. substitute
  have s2 : abs A ≤ abs (A - B) + abs B := by
    have c1 : A - B + B = A := by parley_ring
    have row1 : abs A ≤ abs (A - B) + abs B := by (have h := Eq.subst (motive := (fun t : ℝ => abs t ≤ abs (A - B) + abs B)) c1 s1; push_cast at h ⊢; all_goals exact_mod_cast h)
    exact row1
  -- 3. inequalities
  parley_order

end Parley.Proofs.Setmm.DifferenceOfSizes.DifferenceOfSizes
