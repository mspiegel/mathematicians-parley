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
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Nat.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Core
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.OneOverASumOfThreeRoots

theorem one_over_a_sum_of_three_roots :
    1 / (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) ≠ 0 := by
  -- 1. real arithmetic
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hr3 : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hr5 : Real.sqrt (5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hy1 : 1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ) ≠ 0 := left_ne_zero_of_mul (show (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) * (-(14 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ)) - 46 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + 34 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + 26 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + 61 * Real.sqrt (2 : ℝ) + 55 * Real.sqrt (3 : ℝ) - 53 * Real.sqrt (5 : ℝ) - 93) ≠ 0 by rw [(show (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) * (-(14 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ)) - 46 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) + 34 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + 26 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + 61 * Real.sqrt (2 : ℝ) + 55 * Real.sqrt (3 : ℝ) - 53 * Real.sqrt (5 : ℝ) - 93) = -71 by linear_combination (-(14 * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ)) - 46 * Real.sqrt (3 : ℝ) + 34 * Real.sqrt (5 : ℝ) + 61) * hr2 + (-(14 * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ)) - 46 * Real.sqrt (2 : ℝ) + 26 * Real.sqrt (5 : ℝ) + 55) * hr3 + (-(14 * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) + 34 * Real.sqrt (2 : ℝ) + 26 * Real.sqrt (3 : ℝ) - 53) * hr5)]; norm_num)
  have hv1 : 1 / (1 + Real.sqrt (2 : ℝ) + Real.sqrt (3 : ℝ) + Real.sqrt (5 : ℝ)) = (14 / 71 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + (46 / 71 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) - (34 / 71 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) - (26 / 71 : ℝ) * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) - (61 / 71 : ℝ) * Real.sqrt (2 : ℝ) - (55 / 71 : ℝ) * Real.sqrt (3 : ℝ) + (53 / 71 : ℝ) * Real.sqrt (5 : ℝ) + (93 / 71 : ℝ) := by rw [div_eq_iff hy1]; linear_combination (-((14 / 71 : ℝ) * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ)) - (46 / 71 : ℝ) * Real.sqrt (3 : ℝ) + (34 / 71 : ℝ) * Real.sqrt (5 : ℝ) + (61 / 71 : ℝ)) * hr2 + (-((14 / 71 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ)) - (46 / 71 : ℝ) * Real.sqrt (2 : ℝ) + (26 / 71 : ℝ) * Real.sqrt (5 : ℝ) + (55 / 71 : ℝ)) * hr3 + (-((14 / 71 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ)) + (34 / 71 : ℝ) * Real.sqrt (2 : ℝ) + (26 / 71 : ℝ) * Real.sqrt (3 : ℝ) - (53 / 71 : ℝ)) * hr5
  intro h
  have h0 : (-(1 / 71 : ℝ) : ℝ) = 0 := (show (-(1 / 71 : ℝ) : ℝ) = 0 by linear_combination (-((1 / 71 : ℝ) * Real.sqrt (2 : ℝ)) - (1 / 71 : ℝ) * Real.sqrt (3 : ℝ) - (1 / 71 : ℝ) * Real.sqrt (5 : ℝ) - (1 / 71 : ℝ)) * h + ((1 / 71 : ℝ) * Real.sqrt (2 : ℝ) + (1 / 71 : ℝ) * Real.sqrt (3 : ℝ) + (1 / 71 : ℝ) * Real.sqrt (5 : ℝ) + (1 / 71 : ℝ)) * hv1 + ((14 / 5041 : ℝ) * Real.sqrt (3 : ℝ) * Real.sqrt (5 : ℝ) + (46 / 5041 : ℝ) * Real.sqrt (3 : ℝ) - (34 / 5041 : ℝ) * Real.sqrt (5 : ℝ) - (61 / 5041 : ℝ)) * hr2 + ((14 / 5041 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (5 : ℝ) + (46 / 5041 : ℝ) * Real.sqrt (2 : ℝ) - (26 / 5041 : ℝ) * Real.sqrt (5 : ℝ) - (55 / 5041 : ℝ)) * hr3 + ((14 / 5041 : ℝ) * Real.sqrt (2 : ℝ) * Real.sqrt (3 : ℝ) - (34 / 5041 : ℝ) * Real.sqrt (2 : ℝ) - (26 / 5041 : ℝ) * Real.sqrt (3 : ℝ) + (53 / 5041 : ℝ)) * hr5)
  norm_num at h0

end Parley.Tests.Elaborator.RealArithmetic.OneOverASumOfThreeRoots
