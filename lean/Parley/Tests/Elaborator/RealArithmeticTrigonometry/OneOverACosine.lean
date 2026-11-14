module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-trigonometry.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticTrigonometry.OneOverACosine

theorem one_over_a_cosine :
    Real.cos Real.pi ^ (-1 : ℤ) = -1 := by
  -- 1. real arithmetic
  have hv1 : Real.cos Real.pi = -(1) := by rw [congrArg Real.cos (show Real.pi = 0 + Real.pi by ring1), Real.cos_add_pi, Real.cos_zero]
  have hv2 : Real.cos Real.pi ^ (-1 : ℤ) = -1 := by rw [zpow_neg, zpow_one]; exact inv_eq_of_mul_eq_one_left (show -1 * Real.cos Real.pi = 1 by linear_combination (-1) * hv1)
  linear_combination hv2

end Parley.Tests.Elaborator.RealArithmeticTrigonometry.OneOverACosine
