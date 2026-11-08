module

public import Tactics
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpPositive

theorem exp_positive (x : ℝ) :
    Real.exp x > 0 := by
  -- 1. mun:logarithms-exp-positive
  exact (Parley.Items.Stdlib.Logarithms.mun_exp_positive (x := x))

end Parley.Tests.Stdlib.Logarithms.ExpPositive
