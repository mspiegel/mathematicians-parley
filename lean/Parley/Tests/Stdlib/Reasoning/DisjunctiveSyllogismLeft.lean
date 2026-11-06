module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft

theorem disjunctive_syllogism_left (x : ℝ) (hH2 : x < 0 ∨ x > 0) (hH3 : ¬ x < 0) :
    x > 0 := by
  -- 1. mun:reasoning-disjunctive-syllogism-left, from H2, H3
  have s1 : x > 0 := by first | linarith [(Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) hH3)] | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) hH3); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) hH3) | (have h := (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) (by parley_side) hH3); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft
