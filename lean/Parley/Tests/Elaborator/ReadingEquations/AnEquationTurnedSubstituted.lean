module

public import Tactics

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstituted

theorem an_equation_turned_substituted (x : ℝ) (hH2 : x = 2) :
    2 + 1 = x + 1 := by
  -- 1. substitute 2 = x (H2)
  have s1 : 2 + 1 = x + 1 := by parley_subst hH2
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstituted
