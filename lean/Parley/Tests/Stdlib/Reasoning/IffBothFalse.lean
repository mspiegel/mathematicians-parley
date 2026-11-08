module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Reasoning

/-! Written from tests/stdlib/reasoning.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Reasoning.IffBothFalse

theorem iff_both_false (x : ℝ) (hH2 : x ≠ 0) (hH3 : ¬ x < 0) :
    (x = 0 ↔ x < 0) := by
  -- 1. mun:reasoning-iff-both-false, from H2, H3
  exact (Parley.Items.Stdlib.Reasoning.mun_iff_both_false (P := x = 0) (Q := x < 0) hH2 hH3)

end Parley.Tests.Stdlib.Reasoning.IffBothFalse
