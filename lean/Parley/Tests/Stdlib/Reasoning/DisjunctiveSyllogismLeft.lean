module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft

theorem disjunctive_syllogism_left (x : ℝ) (hH2 : x < 0 ∨ x > 0) (hH3 : ¬ x < 0) :
    x > 0 := by
  -- 1. mun:reasoning-disjunctive-syllogism-left, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft
