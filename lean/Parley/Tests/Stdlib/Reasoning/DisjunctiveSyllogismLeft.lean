module

public import Tactics
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft

theorem disjunctive_syllogism_left (x : ℝ) (hH2 : x < 0 ∨ x > 0) (hH3 : ¬ x < 0) :
    x > 0 := by
  -- 1. mun:reasoning-disjunctive-syllogism-left, from H2, H3
  have s1 : x > 0 := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) (by parley_side)); parley_side)
  all_goals parley_side

end Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft
