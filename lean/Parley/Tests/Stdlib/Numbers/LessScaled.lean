module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LessScaled

theorem less_scaled (x : ℝ) (y : ℝ) (c : ℝ) (hH4 : c > 0) :
    (x < y ↔ c * x < c * y) := by
  -- 1. mun:numbers-less-scaled, from H4
  have s1 : x < y ↔ c * x < c * y := by exact (Parley.Items.Stdlib.Numbers.mun_less_scaled (x := x) (y := y) (c := c) (by parley_side))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.LessScaled
