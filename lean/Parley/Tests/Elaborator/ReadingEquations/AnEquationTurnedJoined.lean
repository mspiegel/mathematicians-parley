module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedJoined

theorem an_equation_turned_joined (a : ℝ) (b : ℝ) (H3 : b = a) :
    a = b := by
  -- 1. restate H3
  have s1 : a = b := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedJoined
