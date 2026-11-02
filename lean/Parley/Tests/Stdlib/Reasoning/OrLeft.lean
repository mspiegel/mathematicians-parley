module

public import LeanBridges
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.OrLeft

theorem or_left (x : ℝ) (hH2 : x = 0) :
    (x = 0 ∨ x = 1) := by
  -- 1. mun:reasoning-or-left, from H2
  have s1 : x = 0 ∨ x = 1 := by first | exact (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) (by parley_side)) | exact ((Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) (by parley_side))).symm | simpa using (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) (by parley_side)) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_or_left (P := x = 0) (Q := x = 1) (by parley_side))
  all_goals parley_side

end Parley.Tests.Stdlib.Reasoning.OrLeft
