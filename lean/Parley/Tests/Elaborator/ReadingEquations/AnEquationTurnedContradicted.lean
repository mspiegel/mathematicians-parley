module

public import Tactics

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedContradicted

theorem an_equation_turned_contradicted (a : ℝ) (b : ℝ) (hH3 : b = a) :
    a = b := by
  -- 1. contradiction
  have s1 : a = b := by
    by_contra hc_hS
    have hS : a ≠ b := by parley_suppose hc_hS
    -- 1.1. restate S
    have s1_1 : a ≠ b := by parley_side
    all_goals parley_side
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedContradicted
