module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLine

theorem a_membership_bound_in_a_requires_line (x : ℝ) (y : ℝ) (c : ℤ) (hH3 : 0 ≤ c) (hH4 : x ≤ y) :
    x * (c : ℝ) ≤ y * (c : ℝ) := by
  -- 1. mun:multiply-le-nonneg, from H4
  have r160_1 : c ≥ 0 := by exact hH3
  exact (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := x) (y := y) (c := (c : ℝ)) hH4 (by exact_mod_cast ge_iff_le.mp r160_1))

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLine
