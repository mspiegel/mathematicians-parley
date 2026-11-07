module

public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpSum

theorem exp_sum (a : ℂ) (b : ℂ) :
    Complex.exp (a + b) = Complex.exp a * Complex.exp b := by
  -- 1. mun:logarithms-exp-sum
  have s1 : Complex.exp (a + b) = Complex.exp a * Complex.exp b := by exact (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b))
  all_goals exact s1

end Parley.Tests.Stdlib.Logarithms.ExpSum
