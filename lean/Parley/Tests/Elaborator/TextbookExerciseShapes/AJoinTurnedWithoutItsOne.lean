module

public import Tactics
public import Mathlib.Basic.Real.Basic

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AJoinTurnedWithoutItsOne

theorem a_join_turned_without_its_one (x : ℝ) (y : ℝ) (hH3 : x * 1 = y) :
    y = x := by
  -- 1. restate H3
  have s1 : y = x := by parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.TextbookExerciseShapes.AJoinTurnedWithoutItsOne
