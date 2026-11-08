module

public import AlgebraTactics
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

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine

theorem a_sine_not_zero_on_a_requires_line (a : ℝ) :
    a * Real.sin (Real.pi / 3) / Real.sin (Real.pi / 3) = a := by
  -- 1. algebra
  have r91_1 : Real.sin (Real.pi / 3) ≠ 0 := by parley_real
  parley_ring

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine
