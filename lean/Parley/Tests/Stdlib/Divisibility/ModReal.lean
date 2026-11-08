module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/stdlib/divisibility.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Divisibility.ModReal

theorem mod_real (a : ℝ) (b : ℝ) (hH3 : b > 0) :
    True := by
  -- 1. mun:divisibility-mod-real, from H3
  exact trivial

end Parley.Tests.Stdlib.Divisibility.ModReal
