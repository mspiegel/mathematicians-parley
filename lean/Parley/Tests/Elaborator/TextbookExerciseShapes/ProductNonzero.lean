module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

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
    have s1_1 : 0 * y = 0 := by ring
    -- 1.2. calculation
    have s1_2 : x * y = 0 * y := by
      calc x * y = 0 := by parley_side
        _ = 0 * y := by parley_side
    -- 1.3. mun:multiply-cancel a := x, b := 0, c := y, from H4, 1.2
    have s1_3 : x = 0 := by linear_combination (Parley.Items.Stdlib.Numbers.mun_multiply_cancel (a := x) (b := (0 : ℝ)) (c := y) (by parley_side) (by parley_side))
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapes.ProductNonzero
