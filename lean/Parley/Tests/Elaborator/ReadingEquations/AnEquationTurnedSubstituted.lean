module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstituted

theorem an_equation_turned_substituted (x : ℝ) (hH2 : x = 2) :
    2 + 1 = x + 1 := by
  -- 1. substitute 2 = x (H2)
  exact congrArg (fun t : ℝ => t + 1) hH2.symm

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstituted
