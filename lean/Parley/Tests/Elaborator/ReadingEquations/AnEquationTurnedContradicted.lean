module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedContradicted

theorem an_equation_turned_contradicted (a : ℝ) (b : ℝ) (H3 : b = a) :
    a = b := by
  -- 1. contradiction
  have s1 : a = b := by
    by_contra hc_S
    have S : a ≠ b := by parley_suppose hc_S
    -- 1.1. restate S
    have s1_1 : a ≠ b := by parley_side
    parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedContradicted
