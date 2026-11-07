module

public import ArithTactics
public import Divisibility
public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/mod-on-the-reals.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ModOnTheReals.OneModAReal

theorem one_mod_a_real (N : ℝ) (hH2 : 1 < N) :
    LeanBridges.Divisibility.mod (1 : ℝ) N = 1 := by
  -- 1. mun:mod-below a := 1, b := N, from H2
  have r11_1 : (0 : ℤ) ≤ 1 := by parley_arith
  have s1 : LeanBridges.Divisibility.mod (1 : ℝ) N = 1 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); simp (disch := positivity) only [LeanBridges.Divisibility.mod_natCast, LeanBridges.Divisibility.mod_intCast] at h ⊢; exact_mod_cast h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_mod_below (a := (1 : ℝ)) (b := N) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ModOnTheReals.OneModAReal
