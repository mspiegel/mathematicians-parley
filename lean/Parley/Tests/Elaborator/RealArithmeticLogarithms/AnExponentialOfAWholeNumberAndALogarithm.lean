module

public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfAWholeNumberAndALogarithm

theorem an_exponential_of_a_whole_number_and_a_logarithm :
    Real.exp (2 + Real.log (3 : ℝ)) = 3 * Real.exp 1 ^ 2 := by
  -- 1. real arithmetic
  have hv1 : Real.exp (2 + Real.log (3 : ℝ)) = Real.exp 1 ^ 2 * 3 := by rw [congrArg Real.exp (show (2 + Real.log (3 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) * 1 + Real.log (3 : ℝ) by ring1), Real.exp_add, Real.exp_nat_mul 1 2, Real.exp_log (show (0 : ℝ) < 3 by norm_num)]
  linear_combination hv1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfAWholeNumberAndALogarithm
