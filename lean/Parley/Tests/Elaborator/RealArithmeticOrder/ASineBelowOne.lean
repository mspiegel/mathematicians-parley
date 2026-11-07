module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ASineBelowOne

theorem a_sine_below_one :
    Real.sin (Real.pi / 4) < 1 := by
  -- 1. real arithmetic
  have s1 : Real.sin (Real.pi / 4) < 1 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.ASineBelowOne
