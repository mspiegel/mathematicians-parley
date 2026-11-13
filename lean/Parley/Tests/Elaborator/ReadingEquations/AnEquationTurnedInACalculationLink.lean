module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInACalculationLink

theorem an_equation_turned_in_a_calculation_link (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b = a) (hH5 : b = c) :
    a = c := by
  -- 1. calculation
  calc a = b := hH4.symm
    _ = c := hH5

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInACalculationLink
