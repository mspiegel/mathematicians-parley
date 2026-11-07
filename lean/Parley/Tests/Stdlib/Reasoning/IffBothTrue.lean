module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffBothTrue

theorem iff_both_true (x : ℝ) (hH2 : x = 0) (hH3 : x ≤ 0) :
    (x = 0 ↔ x ≤ 0) := by
  -- 1. mun:reasoning-iff-both-true, from H2, H3
  have s1 : x = 0 ↔ x ≤ 0 := by exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_true (P := x = 0) (Q := x ≤ 0) hH2 hH3)
  all_goals exact s1

end Parley.Tests.Stdlib.Reasoning.IffBothTrue
