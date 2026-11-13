module

public import RealTactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.ARootNotBelowOne

theorem a_root_not_below_one :
    ¬ Real.sqrt (2 : ℝ) < 1 := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticOrder.ARootNotBelowOne
