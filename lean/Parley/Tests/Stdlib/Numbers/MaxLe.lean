module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.MaxLe

theorem max_le (x : ℝ) (y : ℝ) (z : ℝ) :
    (max x y ≤ z ↔ x ≤ z ∧ y ≤ z) := by
  -- 1. mun:numbers-max-le
  have s1 : max x y ≤ z ↔ x ≤ z ∧ y ≤ z := by exact (Parley.Items.Stdlib.Numbers.mun_max_le (x := x) (y := y) (z := z))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.MaxLe
