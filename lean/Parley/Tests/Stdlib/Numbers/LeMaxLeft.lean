module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LeMaxLeft

theorem le_max_left (x : ℝ) (y : ℝ) :
    x ≤ max x y := by
  -- 1. mun:le-max
  have s1 : x ≤ max x y := by exact (Parley.Items.Stdlib.Numbers.mun_le_max_1 (x := x) (y := y))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.LeMaxLeft
