module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/reading-equations.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstituted

theorem an_equation_turned_substituted (x : ℝ) (hH2 : x = 2) :
    2 + 1 = x + 1 := by
  -- 1. substitute 2 = x (H2)
  (have h := congrArg (fun t : ℝ => t + 1) (hH2).symm; push_cast at h ⊢; all_goals exact_mod_cast h)

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstituted
