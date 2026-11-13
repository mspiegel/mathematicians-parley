module

public import RealTactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring

/-! Written from tests/elaborator/real-arithmetic-logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfALogarithm

theorem an_exponential_of_a_logarithm :
    Real.exp (Real.log (5 : ℝ)) = 5 := by
  -- 1. real arithmetic
  parley_real

end Parley.Tests.Elaborator.RealArithmeticLogarithms.AnExponentialOfALogarithm
