module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.TriangleInequality

theorem triangle_inequality (x : ℝ) (y : ℝ) :
    abs (x + y) ≤ abs x + abs y := by
  -- 1. thm:numbers-triangle-inequality a := x, b := y
  have s1 : abs (x + y) ≤ abs x + abs y := by first | linarith [(Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x) (b := y))] | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x) (b := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x) (b := y)) | (have h := (Parley.Items.Stdlib.Numbers.thm_triangle_inequality (a := x) (b := y)); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.TriangleInequality
