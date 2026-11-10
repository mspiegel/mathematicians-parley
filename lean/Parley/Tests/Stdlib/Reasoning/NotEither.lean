module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.NotEither

theorem not_either (x : ℝ) (hH2 : ¬ (x = 0 ∨ x = 1)) :
    (x ≠ 0 ∧ x ≠ 1) := by
  -- 1. mun:reasoning-not-either, from H2
  have s1 : x ≠ 0 ∧ x ≠ 1 := by exact ((Parley.Items.Stdlib.Reasoning.mun_not_either (P := x = 0) (Q := x = 1))).mp hH2
  exact ⟨(s1).1, (s1).2⟩

end Parley.Tests.Stdlib.Reasoning.NotEither
