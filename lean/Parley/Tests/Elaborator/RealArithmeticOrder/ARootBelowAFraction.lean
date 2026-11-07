module

public import RealTactics
public import Tactics
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ARootBelowAFraction

theorem a_root_below_a_fraction :
    Real.sqrt (2 : ℝ) < 3 / 2 := by
  -- 1. real arithmetic
  have s1 : Real.sqrt (2 : ℝ) < 3 / 2 := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.ARootBelowAFraction
