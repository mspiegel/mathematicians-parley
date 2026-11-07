module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.MaxReal

theorem max_real (x : ℝ) (y : ℝ) :
    True := by
  -- 1. mun:numbers-max-real
  all_goals parley_side

end Parley.Tests.Stdlib.Numbers.MaxReal
