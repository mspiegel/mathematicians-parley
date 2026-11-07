module

public import Divisibility
public import NormTactics
public import PowerTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Rat.Floor
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Set
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/remainder-real.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderReal.RemainderIsReal

theorem remainder_is_real (A : ℝ) (B : ℝ) (hH3 : B > 0) :
    True := by
  -- 1. inequalities
  have s1 : B ≠ 0 := by parley_side
  set q : ℤ := ⌊A / B⌋ with hD1
  have hD1_kind : True := by first | exact (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B))).symm | simpa using (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)) | (have h := (Parley.Items.Stdlib.Numbers.mun_floor_integer (x := A / B)); parley_side)
  -- 2. mun:mod-value a := A, b := B, from D1, H3
  have s2 : LeanBridges.Divisibility.mod A B = A - B * (q : ℝ) := by
    try simp only [hD1] at *
    try push_cast at *
    first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_side)
  -- 3. membership
  -- 4. substitute A mod B = A − B·q (line 2) into line 3
  all_goals parley_side

end Parley.Proofs.Setmm.RemainderReal.RemainderIsReal
