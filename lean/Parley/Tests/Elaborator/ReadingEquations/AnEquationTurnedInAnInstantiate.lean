module

public import Mathlib.Algebra.Group.Monoid
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

namespace Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInAnInstantiate

theorem an_equation_turned_in_an_instantiate (y : ℝ) (hH2 : ∀ x : ℝ, x = x * 1) :
    y * 1 = y := by
  -- 1. instantiate x := y in H2
  simpa only [mul_one] using (hH2 y)

end Parley.Tests.Elaborator.ReadingEquations.AnEquationTurnedInAnInstantiate
