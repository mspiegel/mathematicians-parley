module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Order.Field.Basic
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
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsWhole

theorem a_quotient_of_roots_that_is_whole :
    Real.sqrt (12 : ℝ) / Real.sqrt (3 : ℝ) = 2 := by
  -- 1. real arithmetic
  have hv1 : Real.sqrt (12 : ℝ) = 2 * Real.sqrt (3 : ℝ) := by rw [congrArg Real.sqrt (show (12 : ℝ) = 2 ^ 2 * 3 by ring1), Real.sqrt_mul (show (0 : ℝ) ≤ 2 ^ 2 by positivity) 3, Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hy1 : Real.sqrt (3 : ℝ) ≠ 0 := left_ne_zero_of_mul (show Real.sqrt (3 : ℝ) * -Real.sqrt (3 : ℝ) ≠ 0 by rw [(show Real.sqrt (3 : ℝ) * -Real.sqrt (3 : ℝ) = -3 by linear_combination (-1) * hr3)]; norm_num)
  have hv2 : Real.sqrt (12 : ℝ) / Real.sqrt (3 : ℝ) = 2 := by rw [div_eq_iff hy1]; linear_combination hv1
  linear_combination hv2

end Parley.Tests.Elaborator.RealArithmetic.AQuotientOfRootsThatIsWhole
