module

public import Parley.Library

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnExponentWithoutItsOne

theorem an_exponent_without_its_one (d : ℕ) (hH1 : 0 < d) :
    (2 ^ (d * 1) : ℤ) = 2 ^ d := by
  -- 1. algebra
  have s1 : (2 ^ (d * 1) : ℤ) = 2 ^ d := by ring
  all_goals parley_side

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnExponentWithoutItsOne
