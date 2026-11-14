module

public import RealTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.Field
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

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine

theorem a_sine_not_zero_on_a_requires_line (a : ℝ) :
    a * Real.sin (Real.pi / 3) / Real.sin (Real.pi / 3) = a := by
  -- 1. algebra
  have r91_1 : Real.sin (Real.pi / 3) ≠ 0 := by parley_real
  have hz1 : Real.sin (Real.pi / 3) ≠ 0 := r91_1; field

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.ASineNotZeroOnARequiresLine
