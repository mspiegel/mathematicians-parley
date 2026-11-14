module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootOfASumWithARoot

theorem a_root_of_a_sum_with_a_root :
    Real.sqrt (1 + Real.sqrt (9 : ℝ)) = 2 := by
  -- 1. real arithmetic
  have hv1 : Real.sqrt (9 : ℝ) = 3 := by rw [congrArg Real.sqrt (show (9 : ℝ) = 3 ^ 2 by ring1), Real.sqrt_sq (show (0 : ℝ) ≤ 3 by norm_num)]
  have hv2 : Real.sqrt (1 + Real.sqrt (9 : ℝ)) = 2 := by rw [congrArg Real.sqrt (show (1 + Real.sqrt (9 : ℝ) : ℝ) = 2 ^ 2 by linear_combination hv1), Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  linear_combination hv2

end Parley.Tests.Elaborator.RealArithmetic.ARootOfASumWithARoot
