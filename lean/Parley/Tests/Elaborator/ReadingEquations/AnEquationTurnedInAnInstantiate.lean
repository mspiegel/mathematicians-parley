module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInAnInstantiate

theorem an_equation_turned_in_an_instantiate (y : ℝ) (hH2 : ∀ x : ℝ, x = x * 1) :
    y * 1 = y := by
  -- 1. instantiate x := y in H2
  have s1 : y * 1 = y := by linear_combination (hH2 y)
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInAnInstantiate
