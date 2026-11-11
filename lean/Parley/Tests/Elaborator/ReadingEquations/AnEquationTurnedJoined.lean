module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedJoined

theorem an_equation_turned_joined (a : ℝ) (b : ℝ) (hH3 : b = a) :
    a = b := by
  -- 1. restate H3
  exact hH3.symm

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedJoined
