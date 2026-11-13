module

public import Tactics
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AJoinTurnedWithoutItsOne

theorem a_join_turned_without_its_one (x : ℝ) (y : ℝ) (hH3 : x * 1 = y) :
    y = x := by
  -- 1. restate H3
  simpa only [mul_one] using hH3.symm

end Parley.Tests.Elaborator.TextbookExerciseShapes.AJoinTurnedWithoutItsOne
