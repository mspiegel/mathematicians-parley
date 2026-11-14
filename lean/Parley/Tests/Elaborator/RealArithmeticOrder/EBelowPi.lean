module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds
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
  have hf1 : 3 < Real.pi := Real.pi_gt_three
  have hf2 : Real.pi < 4 := Real.pi_lt_four
  have hf3 : 2 < Real.exp 1 := Real.exp_one_gt_two
  have hf4 : Real.exp 1 < 3 := Real.exp_one_lt_three
  linarith only [hf1, hf2, hf3, hf4]

end Parley.Tests.Elaborator.RealArithmeticOrder.EBelowPi
