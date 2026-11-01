module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInATransitivity

theorem an_equation_turned_in_a_transitivity (a : ℝ) (b : ℝ) (c : ℝ) (H4 : b = a) (H5 : b < c) :
    a < c := by
  -- 1. transitivity, from H4, H5
  have s1 : a < c := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInATransitivity
