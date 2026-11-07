module

public import Tactics
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.TriangleInequality

theorem triangle_inequality (x : ℝ) (y : ℝ) :
    abs (x + y) ≤ abs x + abs y := by
  -- 1. thm:numbers-triangle-inequality a := x, b := y
  have s1 : abs (x + y) ≤ abs x + abs y := by exact (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x) (b := y))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.TriangleInequality
