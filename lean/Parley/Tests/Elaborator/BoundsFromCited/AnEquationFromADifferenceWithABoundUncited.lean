module

public import Parley.Library

/-! Written from tests/elaborator/bounds-from-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.BoundsFromCited.AnEquationFromADifferenceWithABoundUncited

theorem an_equation_from_a_difference_with_a_bound_uncited (a : ℝ) (b : ℝ) (H3 : a ≤ b) (H4 : b - a = 0) :
    a = b := by
  -- 1. inequalities
  have s1 : a = b := by parley_side
  parley_side

end Parley.Tests.Elaborator.BoundsFromCited.AnEquationFromADifferenceWithABoundUncited
