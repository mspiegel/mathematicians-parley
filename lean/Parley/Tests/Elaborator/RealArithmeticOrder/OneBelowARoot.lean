module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.RealSqrt

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowARoot

theorem one_below_a_root :
    1 < Real.sqrt (2 : ℝ) := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticOrder.OneBelowARoot
