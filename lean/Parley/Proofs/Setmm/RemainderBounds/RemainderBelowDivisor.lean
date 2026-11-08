module

public import AlgebraTactics
public import Divisibility
public import OrderTactics
public import SubstTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/remainder-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor

theorem remainder_below_divisor (A : ℝ) (B : ℝ) (hH3 : B > 0) :
    LeanBridges.Divisibility.mod A B < B := by
  -- 1. inequalities
  have s1 : B ≠ 0 := by parley_side
  set q : ℤ := ⌊A / B⌋ with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)); parley_side)
  -- 2. mun:mod-value a := A, b := B, from D1, H3
  have s2 : LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) hH3)
  -- 3. mun:floor-above x := A/B, from D1, 1
  have s3 : A / B < (q : ℝ) + 1 := by
    try simp only [hD1] at *
    try push_cast at *
    exact (Parley.Items.Stdlib.Numbers.mun_floor_above (x := A / B))
  -- 4. calculation
  have s4 : A < B * (q : ℝ) + B := by
    calc A = B * (A / B) := by parley_ring
      _ < B * ((q : ℝ) + 1) := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := A / B) (y := (q : ℝ) + 1) (c := B) (by parley_side))).mp s3
      _ = B * (q : ℝ) + B := by parley_ring
  -- 5. inequalities
  have s5 : A - B * (q : ℝ) < B := by parley_order
  -- 6. substitute A mod B = A − B·q (line 2) into line 5
  parley_subst_at s2 s5

end Parley.Proofs.Setmm.RemainderBounds.RemainderBelowDivisor
