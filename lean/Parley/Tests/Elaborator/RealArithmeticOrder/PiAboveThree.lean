module

public import RealTactics
public import Tactics
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiAboveThree

theorem pi_above_three :
    3 < Real.pi := by
  -- 1. real arithmetic
  have s1 : 3 < Real.pi := by parley_real
  all_goals exact s1

end Parley.Tests.Elaborator.RealArithmeticOrder.PiAboveThree
