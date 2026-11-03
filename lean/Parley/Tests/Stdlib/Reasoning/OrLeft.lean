module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.OrLeft

theorem or_left (x : ℝ) (hH2 : x = 0) :
    (x = 0 ∨ x = 1) := by
  -- 1. mun:reasoning-or-left, from H2
  have s1 : x = 0 ∨ x = 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) hH2) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) hH2)).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) hH2) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) hH2) | (have h := (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) hH2); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.OrLeft
