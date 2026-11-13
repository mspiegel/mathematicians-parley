module

public import AlgebraTactics
public import RealTactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-in-place.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticInPlace.ARequiresLineByRealArithmetic

theorem a_requires_line_by_real_arithmetic (a : ℝ) :
    a * (Real.sqrt (2 : ℝ) - 1) / (Real.sqrt (2 : ℝ) - 1) = a := by
  -- 1. algebra
  have r25_1 : Real.sqrt (2 : ℝ) - 1 ≠ 0 := by parley_real
  parley_ring

end Parley.Tests.Elaborator.RealArithmeticInPlace.ARequiresLineByRealArithmetic
