module

public import RealTactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi

theorem e_below_pi :
    Real.exp 1 < Real.pi := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi
