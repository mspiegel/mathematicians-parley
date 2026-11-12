module

public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/inequality-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.InequalityRows.HalfwayAbove

theorem halfway_above (A : ℝ) (B : ℝ) (hH3 : A < B) :
    A < (A + B) / 2 := by
  -- 1. inequalities
  linarith only [hH3]

end Parley.Tests.Elaborator.InequalityRows.HalfwayAbove
