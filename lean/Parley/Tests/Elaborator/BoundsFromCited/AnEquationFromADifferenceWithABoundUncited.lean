module

public import Tactics

/-! Written from tests/elaborator/bounds-from-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundsFromCited.AnEquationFromADifferenceWithABoundUncited

theorem an_equation_from_a_difference_with_a_bound_uncited (a : ℝ) (b : ℝ) (hH3 : a ≤ b) (hH4 : b - a = 0) :
    a = b := by
  -- 1. inequalities
  have s1 : a = b := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.BoundsFromCited.AnEquationFromADifferenceWithABoundUncited
