module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInATransitivity

theorem an_equation_turned_in_a_transitivity (a : ℝ) (b : ℝ) (c : ℝ) (hH4 : b = a) (hH5 : b < c) :
    a < c := by
  -- 1. transitivity, from H4, H5
  have s1 : a < c := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInATransitivity
