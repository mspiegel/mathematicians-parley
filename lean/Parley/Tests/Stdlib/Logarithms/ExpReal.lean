module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.ExpReal

theorem exp_real (x : ℝ) :
    True := by
  -- 1. mun:logarithms-exp-real
  exact trivial

end Parley.Tests.Stdlib.Logarithms.ExpReal
