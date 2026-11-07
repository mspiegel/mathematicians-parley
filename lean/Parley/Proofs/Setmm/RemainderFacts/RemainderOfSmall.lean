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
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/remainder-facts.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall

theorem remainder_of_small (A : ℝ) (B : ℝ) (hH3 : B > 0) (hH4 : 0 ≤ A) (hH5 : A < B) :
    LeanBridges.Divisibility.mod A B = A := by
  -- 1. mun:quotient-nonneg x := A, y := B, from H3, H4
  have s1 : 0 ≤ A / B := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := A) (y := B) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := A) (y := B) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := A) (y := B) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_quotient_nonneg (x := A) (y := B) (by parley_side) (by parley_side)); parley_side)
  -- 2. algebra
  have r51_1 : B ≠ 0 := by parley_side
  have s2 : B * (A / B) = A := by parley_ring
  -- 3. transitivity, from 2, H5
  have r55_1 : B ≠ 0 := by parley_side
  have s3 : B * (A / B) < B := by parley_order
  -- 4. mun:less-scaled x := A/B, y := 1, c := B, from H3, 3
  have s4 : A / B < 1 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := A / B) (y := (1 : ℝ)) (c := B) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := A / B) (y := (1 : ℝ)) (c := B) (by parley_side))).mpr (by parley_side); parley_side)
  -- 5. mun:floor-between x := A/B, k := 0, from 1, 4
  have r62_1 : B ≠ 0 := by parley_side
  have s5 : ⌊A / B⌋ = 0 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := A / B) (k := (0 : ℤ)))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_floor_between (x := A / B) (k := (0 : ℤ)))).mpr (by parley_side); parley_side)
  -- 6. calculation
  have s6 : LeanBridges.Divisibility.mod A B = A := by
    calc LeanBridges.Divisibility.mod A B = A - B * (⌊A / B⌋ : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := B) (by parley_side)); parley_side)
      _ = A - B * 0 := by
          have s5_w : (⌊A / B⌋ : ℝ) = 0 := by have h := congrArg (fun x : ℤ => (x : ℝ)) s5; push_cast at h; linear_combination (norm := parley_norm) h
          first | parley_subst s5_w | parley_subst s5
      _ = A := by parley_ring
  all_goals exact s6

end Parley.Proofs.Setmm.RemainderFacts.RemainderOfSmall
