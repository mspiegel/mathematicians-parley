module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-order.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticOrder.PiSquaredBelowSixteen

theorem pi_squared_below_sixteen :
    Real.pi ^ 2 < 16 := by
  -- 1. real arithmetic
  have hf1 : 3 < Real.pi := Real.pi_gt_three
  have hf2 : Real.pi < 4 := Real.pi_lt_four
  have hf3 : 3 ^ 2 < Real.pi ^ 2 := pow_lt_pow_left₀ hf1 (show (0 : ℝ) ≤ 3 by norm_num) (show 2 ≠ 0 by norm_num)
  have hf4 : Real.pi ^ 2 < 4 ^ 2 := pow_lt_pow_left₀ hf2 (le_of_lt (lt_of_le_of_lt (show (0 : ℝ) ≤ 3 by norm_num) hf1)) (show 2 ≠ 0 by norm_num)
  linarith only [hf3, hf4]

end Parley.Tests.Elaborator.RealArithmeticOrder.PiSquaredBelowSixteen
