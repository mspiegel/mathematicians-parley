module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
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
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmetic.ARootAgainstANegativePowerOfNumerals

theorem a_root_against_a_negative_power_of_numerals :
    Real.sqrt (2 : ℝ) ≠ 3 ^ (-1 : ℤ) := by
  -- 1. real arithmetic
  have hv1 : 3 ^ (-1 : ℤ) = (1 / 3 : ℝ) := by rw [zpow_neg, zpow_one]; exact inv_eq_of_mul_eq_one_left (show (1 / 3 : ℝ) * 3 = 1 by ring1)
  have hr2 : Real.sqrt (2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  intro h
  have h0 : (-(17 / 9 : ℝ) : ℝ) = 0 := (show (-(17 / 9 : ℝ) : ℝ) = 0 by linear_combination (-Real.sqrt (2 : ℝ) - (1 / 3 : ℝ)) * h + (-Real.sqrt (2 : ℝ) - (1 / 3 : ℝ)) * hv1 + hr2)
  norm_num at h0

end Parley.Tests.Elaborator.RealArithmetic.ARootAgainstANegativePowerOfNumerals
