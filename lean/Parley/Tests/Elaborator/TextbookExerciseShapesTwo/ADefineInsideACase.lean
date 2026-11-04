module

public import ArithTactics
public import OrderTactics
public import Tactics

/-! Written from tests/elaborator/textbook-exercise-shapes-two.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ADefineInsideACase

theorem a_define_inside_a_case (x : ℝ) (hH2 : x = 1 ∨ x = 2) :
    x > 0 := by
  -- 1. cases, from H2
  have s1 : x > 0 := by
    rcases hH2 with hC1 | hC2
    · skip
      set y : ℝ := x with hD1
      -- 1.1. D1
      have s1_1 : y = x := by parley_side
      -- 1.2. arithmetic
      have s1_2 : (1 : ℤ) > 0 := by parley_arith
      -- 1.3. transitivity, from 1.1, C1, 1.2
      have s1_3 : y > 0 := by parley_order
      -- 1.4. transitivity, from 1.1, 1.3
      have s1_4 : x > 0 := by parley_order
      all_goals parley_side
    · skip
      -- 1.5. arithmetic
      have s1_5 : (2 : ℤ) > 0 := by parley_arith
      -- 1.6. transitivity, from C2, 1.5
      have s1_6 : x > 0 := by parley_order
      all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.TextbookExerciseShapesTwo.ADefineInsideACase
