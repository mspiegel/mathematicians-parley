module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Positivity.Basic
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpSum

theorem exp_sum (a : ℂ) (b : ℂ) :
    Complex.exp (a + b) = Complex.exp a * Complex.exp b := by
  -- 1. mun:logarithms-exp-sum
  exact (Parley.Items.Stdlib.Logarithms.mun_exp_sum (a := a) (b := b))

end Parley.Tests.Stdlib.Logarithms.ExpSum
