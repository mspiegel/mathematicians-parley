module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineInTheThirdQuadrant

theorem a_sine_in_the_third_quadrant :
    Real.sin (7 * Real.pi / 6) = -(1 / 2) := by
  -- 1. real arithmetic
  have s1 : Real.sin (7 * Real.pi / 6) = -(1 / 2) := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineInTheThirdQuadrant
