module

public import SubstTactics
public import Tactics

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstitutedInto

theorem an_equation_turned_substituted_into (x : ℝ) (y : ℝ) (hH3 : x + 1 = y) (hH4 : x = 2) :
    y = 2 + 1 := by
  -- 1. substitute x = 2 (H4) into H3
  have s1 : y = 2 + 1 := by parley_subst_at hH4 hH3
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstitutedInto
