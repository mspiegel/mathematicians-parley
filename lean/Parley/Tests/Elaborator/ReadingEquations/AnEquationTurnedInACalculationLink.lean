module

public import Parley.Library

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInACalculationLink

theorem an_equation_turned_in_a_calculation_link (a : ℝ) (b : ℝ) (c : ℝ) (H4 : b = a) (H5 : b = c) :
    a = c := by
  -- 1. calculation
  have s1 : a = c := by
    calc a = b := by parley_side
      _ = c := by parley_side
  parley_side

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInACalculationLink
