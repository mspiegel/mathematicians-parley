module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstitutedInto

theorem an_equation_turned_substituted_into (x : ℝ) (y : ℝ) (H3 : x + 1 = y) (H4 : x = 2) :
    y = 2 + 1 := by
  -- 1. substitute x = 2 (H4) into H3
  have s1 : y = 2 + 1 := by parley_subst_at H4 H3
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstitutedInto
