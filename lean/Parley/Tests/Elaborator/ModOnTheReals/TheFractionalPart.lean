module

public import ArithTactics
public import Divisibility
public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
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
public import Parley.Items.Stdlib.Divisibility
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/mod-on-the-reals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ModOnTheReals.TheFractionalPart

theorem the_fractional_part (A : ℝ) :
    LeanBridges.Divisibility.mod A (1 : ℝ) = A - (⌊A⌋ : ℝ) := by
  -- 1. mun:mod-value a := A, b := 1
  have r20_1 : (1 : ℤ) > 0 := by parley_arith
  have s1 : LeanBridges.Divisibility.mod A (1 : ℝ) = A - (⌊A⌋ : ℝ) := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_value (a := A) (b := (1 : ℝ)) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ModOnTheReals.TheFractionalPart
