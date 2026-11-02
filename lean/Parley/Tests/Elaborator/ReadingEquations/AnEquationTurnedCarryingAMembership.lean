module

public import Tactics

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership

theorem an_equation_turned_carrying_a_membership (x : ℂ) (r : ℝ) (hH3 : (r : ℂ) = x) :
    (∃ m : ℝ, (m : ℂ) = x) := by
  -- 1. membership, from H3
  have s1 : ∃ m : ℝ, (m : ℂ) = x := ⟨r, by first | (push_cast; linarith [hH3]) | (rw [hH3]; push_cast; ring) | (rw [← hH3]; push_cast; ring) | exact hH3 | exact hH3.symm⟩
  all_goals parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedCarryingAMembership
