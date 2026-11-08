module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LeMaxRight

theorem le_max_right (x : ℝ) (y : ℝ) :
    y ≤ max x y := by
  -- 1. mun:le-max
  exact (Parley.Items.Stdlib.Numbers.mun_le_max_2 (x := x) (y := y))

end Parley.Tests.Stdlib.Numbers.LeMaxRight
