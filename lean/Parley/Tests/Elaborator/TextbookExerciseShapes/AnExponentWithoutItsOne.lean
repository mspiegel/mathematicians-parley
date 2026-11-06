module

public import AlgebraTactics
public import Tactics

/-! Written from tests/elaborator/textbook-exercise-shapes.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.TextbookExerciseShapes.AnExponentWithoutItsOne

theorem an_exponent_without_its_one (d : ℤ) (hH1 : 0 < d) :
    (2 ^ (d * 1).toNat : ℤ) = 2 ^ d.toNat := by
  -- 1. algebra
  have s1 : (2 ^ (d * 1).toNat : ℤ) = 2 ^ d.toNat := by parley_ring
  all_goals exact s1

end Parley.Tests.Elaborator.TextbookExerciseShapes.AnExponentWithoutItsOne
