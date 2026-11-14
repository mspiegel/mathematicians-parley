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
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAPowerOfE

theorem a_logarithm_of_a_power_of_e :
    Real.log (Real.exp 1 ^ 3) = 3 := by
  -- 1. real arithmetic
  have hv1 : Real.log (Real.exp 1 ^ 3) = ((3 : ℕ) : ℝ) * 1 := by rw [Real.log_pow (Real.exp 1) 3, Real.log_exp 1]
  linear_combination hv1

end Parley.Tests.Elaborator.RealArithmeticLogarithms.ALogarithmOfAPowerOfE
