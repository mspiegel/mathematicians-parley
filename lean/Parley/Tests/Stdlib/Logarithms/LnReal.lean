module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Logarithms

/-! Written from tests/stdlib/logarithms.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Logarithms.LnReal

theorem ln_real (x : ℝ) (hH2 : x > 0) :
    True := by
  -- 1. mun:logarithms-ln-real, from H2
  exact trivial

end Parley.Tests.Stdlib.Logarithms.LnReal
