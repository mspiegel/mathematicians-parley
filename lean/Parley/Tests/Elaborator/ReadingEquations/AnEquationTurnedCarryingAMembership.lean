module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership

theorem an_equation_turned_carrying_a_membership (x : ℂ) (r : ℝ) (H3 : (r : ℂ) = x) :
    (∃ m : ℝ, (m : ℂ) = x) := by
  -- 1. membership, from H3
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership
