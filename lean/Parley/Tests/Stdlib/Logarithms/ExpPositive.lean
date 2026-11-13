module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpPositive

theorem exp_positive (x : ℝ) :
    Real.exp x > 0 := by
  -- 1. mun:logarithms-exp-positive
  exact (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := x))

end Parley.Tests.Stdlib.Logarithms.ExpPositive
