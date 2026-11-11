module

public import OrderTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers
public import Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds

/-! Written from proofs/setmm/bounded-by-square.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.BoundedBySquare.BoundedBySquare

theorem bounded_by_square (A : ℝ) (B : ℝ) (hH3 : 0 ≤ B) :
    (A ≤ B ∧ -A ≤ B ↔ A ^ 2 ≤ B ^ 2) := by
  -- 1. thm:abs-bounds x := A
  have s1a : A ≤ abs A := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).1
  have s1b : -A ≤ abs A := by exact (Parley.Proofs.Wiedijk.TriangleInequality.AbsBounds.abs_bounds (x := A)).2
  -- 2. mun:abs-square x := A
  have s2 : abs A ^ 2 = A ^ 2 := by exact (Parley.Items.Stdlib.Numbers.mun_abs_square (x := A))
  -- 3. inequalities, from 1
  have s3 : 0 ≤ 2 * abs A := by parley_order
  -- 4. inequalities
  have s4 : 0 ≤ abs A := by parley_order
  -- 5. mun:nonneg-or-neg x := A
  have s5 : A ≥ 0 ∨ A < 0 := by exact (Parley.Items.Stdlib.Numbers.mun_nonneg_or_neg (x := A))
  -- 6. both directions
  constructor
  · skip
    intro hD1
    -- 6.1. cases, from 5
    have s6_1 : abs A ≤ B := by
      rcases s5 with hC1 | hC2
      · skip
        -- 6.1.1. def:abs x := A, from C1
        have s6_1_1 : abs A = A := by exact (Parley.Items.Stdlib.Numbers.def_abs_1 (x := A)) hC1
        -- 6.1.2. transitivity, from 6.1.1, D1
        parley_order
      · skip
        -- 6.1.3. def:abs x := A, from C2
        have s6_1_3 : abs A = -A := by exact (Parley.Items.Stdlib.Numbers.def_abs_2 (x := A)) hC2
        -- 6.1.4. transitivity, from 6.1.3, D1
        parley_order
    -- 6.2. contradiction
    by_contra hS1
    -- 6.2.1. inequalities, from S1
    have s6_2_1 : B ^ 2 < A ^ 2 := by parley_order
    -- 6.2.2. substitute |A|² = A² (line 2) into line 6.2.1
    have s6_2_2 : B ^ 2 < abs A ^ 2 := by (have h := Eq.subst (motive := (fun t : ℝ => B ^ 2 < t)) s2.symm s6_2_1; push_cast at h ⊢; all_goals exact_mod_cast h)
    -- 6.2.3. mun:square-less x := B, y := |A|, from 6.2.2
    have r70_1 : abs A ≥ 0 := by parley_side
    have r70_2 : B ≥ 0 := by parley_side
    have s6_2_3 : B < abs A := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) r70_2 r70_1)).mpr s6_2_2
    -- 6.2.4. inequalities, from 6.2.3
    have s6_2_4 : ¬ abs A ≤ B := by parley_side
    exact s6_2_4 s6_1
  · skip
    intro hD2
    -- 6.3. contradiction
    have s6_3 : abs A ≤ B := by
      by_contra hS2
      -- 6.3.1. inequalities, from S2
      have s6_3_1 : B < abs A := by parley_order
      -- 6.3.2. mun:square-less x := B, y := |A|, from 6.3.1
      have r88_1 : abs A ≥ 0 := by parley_side
      have r88_2 : B ≥ 0 := by parley_side
      have s6_3_2 : B ^ 2 < abs A ^ 2 := by exact ((Parley.Items.Stdlib.Numbers.mun_square_less (x := B) (y := abs A) r88_2 r88_1)).mp s6_3_1
      -- 6.3.3. substitute |A|² = A² (line 2) into line 6.3.2
      have s6_3_3 : B ^ 2 < A ^ 2 := by (have h := Eq.subst (motive := (fun t : ℝ => B ^ 2 < t)) s2 s6_3_2; push_cast at h ⊢; all_goals exact_mod_cast h)
      -- 6.3.4. inequalities, from 6.3.3
      have s6_3_4 : ¬ A ^ 2 ≤ B ^ 2 := by parley_side
      exact s6_3_4 hD2
    -- 6.4. inequalities, from 1
    have s6_4 : A ≤ abs A := by parley_order
    -- 6.5. transitivity, from 6.4, 6.3
    have s6_5 : A ≤ B := by parley_order
    -- 6.6. inequalities, from 1
    have s6_6 : -A ≤ abs A := by parley_order
    -- 6.7. transitivity, from 6.6, 6.3
    have s6_7 : -A ≤ B := by parley_order
    -- 6.8. join 6.5, 6.7
    have s6_8 : A ≤ B ∧ -A ≤ B := by parley_side
    exact ⟨(s6_8).1, (s6_8).2⟩

end Parley.Proofs.Setmm.BoundedBySquare.BoundedBySquare
