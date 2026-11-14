module

public import AlgebraTactics
public import Divisibility
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/remainder-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative

theorem remainder_nonnegative (A : ℝ) (B : ℝ) (hH3 : B > 0) :
    0 ≤ LeanBridges.Divisibility.mod A B := by
  -- 1. inequalities
  have s1 : B ≠ 0 := ne_of_gt (by linarith only [hH3])
  set q : ℤ := ⌊A / B⌋ with hD1
  -- 2. mun:mod-value a := A, b := B, from D1, H3
  have s2 : LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) hH3)
  -- 3. mun:floor-below x := A/B, from D1, 1
  have s3 : (q : ℝ) ≤ A / B := by
    simp only [hD1] at ⊢
    push_cast at ⊢
    exact (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A / B))
  -- 4. calculation
  have s4 : B * (q : ℝ) ≤ A := by
    calc B * (q : ℝ) ≤ B * (A / B) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (q : ℝ)) (y := A / B) (c := B) s3 hH3)
      _ = A := by parley_ring
  -- 5. inequalities
  have s5 : 0 ≤ A - B * (q : ℝ) := by linarith only [s4]
  -- 6. substitute A mod B = A − B·q (line 2) into line 5
  exact Eq.subst (motive := (fun t : ℝ => 0 ≤ t)) s2.symm s5

end Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative
