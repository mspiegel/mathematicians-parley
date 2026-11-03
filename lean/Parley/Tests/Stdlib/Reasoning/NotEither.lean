module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.NotEither

theorem not_either (x : ℝ) (hH2 : ¬ (x = 0 ∨ x = 1)) :
    (x ≠ 0 ∧ x ≠ 1) := by
  -- 1. mun:reasoning-not-either, from H2
  have s1 : x ≠ 0 ∧ x ≠ 1 := by first | exact ((Parley.Items.Stdlib.Reasoning.mun_not_either (P := x = 0) (Q := x = 1))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Reasoning.mun_not_either (P := x = 0) (Q := x = 1))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Reasoning.mun_not_either (P := x = 0) (Q := x = 1))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Reasoning.mun_not_either (P := x = 0) (Q := x = 1))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Reasoning.mun_not_either (P := x = 0) (Q := x = 1))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.NotEither
