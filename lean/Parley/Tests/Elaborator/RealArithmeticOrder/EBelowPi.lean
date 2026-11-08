module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi

theorem e_below_pi :
    Real.exp 1 < Real.pi := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi
