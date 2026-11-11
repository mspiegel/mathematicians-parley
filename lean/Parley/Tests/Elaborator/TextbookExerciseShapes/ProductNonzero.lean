module

public import AlgebraTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero

theorem product_nonzero (x : ℝ) (y : ℝ) (hH3 : x ≠ 0) (hH4 : y ≠ 0) :
    x * y ≠ 0 := by
  -- 1. contradiction
  intro hS
  -- 1.1. algebra
  have s1_1 : 0 * y = 0 := by parley_ring
  -- 1.2. calculation
  have s1_2 : x * y = 0 * y := by
    calc x * y = 0 := by parley_side
      _ = 0 * y := by exact s1_1.symm
  -- 1.3. mun:multiply-cancel a := x, b := 0, c := y, from H4, 1.2
  have s1_3 : x = 0 := by exact (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) hH4)
  exact hH3 s1_3

end Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero
