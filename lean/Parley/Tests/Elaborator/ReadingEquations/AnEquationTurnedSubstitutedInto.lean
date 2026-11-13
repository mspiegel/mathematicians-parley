module

public import SubstTactics
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

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstitutedInto

theorem an_equation_turned_substituted_into (x : ℝ) (y : ℝ) (hH3 : x + 1 = y) (hH4 : x = 2) :
    y = 2 + 1 := by
  -- 1. substitute x = 2 (H4) into H3
  parley_subst_at hH4 hH3

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedSubstitutedInto
