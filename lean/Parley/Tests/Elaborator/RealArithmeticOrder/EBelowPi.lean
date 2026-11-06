module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi

theorem e_below_pi :
    Real.exp 1 < Real.pi := by
  -- 1. real arithmetic
  have s1 : Real.exp 1 < Real.pi := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi
