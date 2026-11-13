module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.ModEq
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Rify
public import Mathlib.Tactic.Ring
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft

theorem disjunctive_syllogism_left (x : ℝ) (hH2 : x < 0 ∨ x > 0) (hH3 : ¬ x < 0) :
    x > 0 := by
  -- 1. mun:reasoning-disjunctive-syllogism-left, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_disjunctive_syllogism_left (P := x < 0) (Q := 0 < x) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.DisjunctiveSyllogismLeft
