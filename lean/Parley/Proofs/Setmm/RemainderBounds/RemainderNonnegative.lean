module

public import AlgebraTactics
public import Divisibility
public import NormTactics
public import OrderTactics
public import PowerTactics
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
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/remainder-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative

theorem remainder_nonnegative (A : ℝ) (B : ℝ) (hH3 : B > 0) :
    0 ≤ LeanBridges.Divisibility.mod A B := by
  -- 1. inequalities
  have s1 : B ≠ 0 := by parley_side
  set q : ℤ := ⌊A / B⌋ with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)); parley_side)
  -- 2. mun:mod-value a := A, b := B, from D1, H3
  have s2 : LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_side)
  -- 3. mun:floor-below x := A/B, from D1, 1
  have s3 : (q : ℝ) ≤ A / B := by
    try simp only [hD1] at *
    try push_cast at *
    first | linarith [(Parley.Items.Stdlib.Numbers.mun_floor_below (x := A / B))] | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A / B)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A / B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_below (x := A / B)); parley_side)
  -- 4. calculation
  have s4 : B * (q : ℝ) ≤ A := by
    calc B * (q : ℝ) ≤ B * (A / B) := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := (q : ℝ)) (y := A / B) (c := B) (by parley_side) (by parley_side))
      _ = A := by parley_ring
  -- 5. inequalities
  have s5 : 0 ≤ A - B * (q : ℝ) := by parley_order
  -- 6. substitute A mod B = A − B·q (line 2) into line 5
  have s6 : 0 ≤ LeanBridges.Divisibility.mod A B := by parley_subst_at s2 s5
  all_goals exact s6

end Parley.Proofs.Setmm.RemainderBounds.RemainderNonnegative
