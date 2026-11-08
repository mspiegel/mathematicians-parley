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

/-! Written from proofs/setmm/difference-of-magnitudes.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.DifferenceOfMagnitudes.DifferenceOfMagnitudes

set_option maxHeartbeats 400000 in
theorem difference_of_magnitudes (A : ℝ) (B : ℝ) :
    abs (abs A - abs B) ≤ abs (A - B) := by
  -- 1. thm:triangle-inequality a := A − B, b := B
  have s1 : abs (A - B + B) ≤ abs (A - B) + abs B := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := A - B) (b := B))
  -- 2. substitute
  have s2 : abs A ≤ abs (A - B) + abs B := by
    have c1 : A - B + B = A := by parley_ring
    have row1 : abs A ≤ abs (A - B) + abs B := by parley_subst_at c1 s1
    exact row1
  -- 3. thm:triangle-inequality a := B − A, b := A
  have s3 : abs (B - A + A) ≤ abs (B - A) + abs A := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := B - A) (b := A))
  -- 4. substitute
  have s4 : abs B ≤ abs (B - A) + abs A := by
    have c1 : B - A + A = B := by parley_ring
    have row1 : abs B ≤ abs (B - A) + abs A := by parley_subst_at c1 s3
    exact row1
  -- 5. mun:abs-negative x := A − B
  have s5 : abs (-(A - B)) = abs (A - B) := by exact (Parley.Items.Stdlib.Numbers.mun_abs_negative (x := A - B))
  -- 6. substitute
  have s6 : abs (B - A) = abs (A - B) := by
    have c1 : -(A - B) = B - A := by parley_ring
    have row1 : abs (B - A) = abs (A - B) := by parley_subst_at c1 s5
    exact row1
  -- 7. mun:nonneg-or-neg x := |A| − |B|
  have s7 : abs A - abs B ≥ 0 ∨ abs A - abs B < 0 := (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := abs A - abs B))
  -- 8. cases, from 7
  rcases s7 with hC1 | hC2
  · skip
    -- 8.1. inequalities
    have s8_1 : abs A - abs B ≤ abs (A - B) := by parley_order
    -- 8.2. calculation
    calc abs (abs A - abs B) = abs A - abs B := (Parley.Items.Stdlib.Numbers.def_abs_1 (x := abs A - abs B)) hC1
      _ ≤ abs (A - B) := by parley_side
  · skip
    -- 8.3. substitute |B − A| = |A − B| (line 6) into line 4
    have s8_3 : abs B ≤ abs (A - B) + abs A := by parley_subst_at s6 s4
    -- 8.4. inequalities
    have s8_4 : -(abs A - abs B) ≤ abs (A - B) := by parley_order
    -- 8.5. calculation
    calc abs (abs A - abs B) = -(abs A - abs B) := (Parley.Items.Stdlib.Numbers.def_abs_2 (x := abs A - abs B)) hC2
      _ ≤ abs (A - B) := by parley_side

end Parley.Proofs.Setmm.DifferenceOfMagnitudes.DifferenceOfMagnitudes
