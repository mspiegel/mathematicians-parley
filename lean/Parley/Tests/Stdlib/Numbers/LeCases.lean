module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/stdlib/numbers.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Numbers.LeCases

theorem le_cases (x : ℝ) (y : ℝ) :
    (x ≤ y ↔ x < y ∨ x = y) := by
  -- 1. mun:numbers-le-cases
  have s1 : x ≤ y ↔ x < y ∨ x = y := by exact (Parley.Items.Stdlib.Numbers.mun_le_cases (x := x) (y := y))
  all_goals exact s1

end Parley.Tests.Stdlib.Numbers.LeCases
