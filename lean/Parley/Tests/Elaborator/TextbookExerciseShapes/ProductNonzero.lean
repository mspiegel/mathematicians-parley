module

public import AlgebraTactics
public import ArithTactics
public import NormTactics
public import PowerTactics
public import RealTactics
public import Tactics
public import Batteries.Tactic.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero

theorem product_nonzero (x : ℝ) (y : ℝ) (hH3 : x ≠ 0) (hH4 : y ≠ 0) :
    x * y ≠ 0 := by
  -- 1. contradiction
  have s1 : x * y ≠ 0 := by
    by_contra hc_hS
    have hS : x * y = 0 := by parley_suppose hc_hS
    -- 1.1. algebra
    have s1_1 : 0 * y = 0 := by parley_ring
    -- 1.2. calculation
    have s1_2 : x * y = 0 * y := by
      calc x * y = 0 := by parley_side
        _ = 0 * y := by parley_side
    -- 1.3. mun:multiply-cancel a := x, b := 0, c := y, from H4, 1.2
    have s1_3 : x = 0 := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); parley_rat_of_real h) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side)); parley_side)
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero
