module

public import AlgebraTactics
public import OrderTactics
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
public import Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow

/-! Written from proofs/setmm/reverse-triangle-inequality.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceOfAbs

set_option maxHeartbeats 400000 in
theorem abs_difference_of_abs (A : ℝ) (B : ℝ) :
    abs (abs A - abs B) ≤ abs (A - B) := by
  -- 1. thm:abs-difference-below
  have s1 : abs A - abs B ≤ abs (A - B) := by exact (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := A) (B := B))
  -- 2. thm:abs-difference-below A := B, B := A
  have s2 : abs B - abs A ≤ abs (B - A) := by exact (Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceBelow.abs_difference_below (A := B) (B := A))
  -- 3. mun:abs-negative x := A − B
  have s3 : abs (-(A - B)) = abs (A - B) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B))
  -- 4. substitute
  have s4 : abs (B - A) = abs (A - B) := by
    have c1 : -(A - B) = B - A := by parley_ring
    have row1 : abs (B - A) = abs (A - B) := by parley_subst_at c1 s3
    exact row1
  -- 5. substitute |B − A| = |A − B| (line 4) into line 2
  have s5 : abs B - abs A ≤ abs (A - B) := by (have h := Eq.subst (motive := (fun t : ℝ => abs B - abs A ≤ t)) s4 s2; push_cast at h ⊢; all_goals exact_mod_cast h)
  -- 6. mun:nonneg-or-neg x := |A| − |B|
  have s6 : abs A - abs B ≥ 0 ∨ abs A - abs B < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B))
  -- 7. cases, from 6
  rcases s6 with hC1 | hC2
  · skip
    -- 7.1. def:abs x := |A| − |B|, from C1
    have s7_1 : abs (abs A - abs B) = abs A - abs B := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) hC1
    -- 7.2. transitivity, from 7.1, 1
    parley_order
  · skip
    -- 7.3. def:abs x := |A| − |B|, from C2
    have s7_3 : abs (abs A - abs B) = -(abs A - abs B) := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) hC2
    -- 7.4. inequalities
    have s7_4 : -(abs A - abs B) ≤ abs (A - B) := by parley_order
    -- 7.5. transitivity, from 7.3, 7.4
    parley_order

end Parley.Proofs.Setmm.ReverseTriangleInequality.AbsDifferenceOfAbs
