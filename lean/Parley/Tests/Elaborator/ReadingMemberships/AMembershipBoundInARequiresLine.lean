module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Notation
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLine

theorem a_membership_bound_in_a_requires_line (x : ℝ) (y : ℝ) (c : ℤ) (hH3 : 0 ≤ c) (hH4 : x ≤ y) :
    x * (c : ℝ) ≤ y * (c : ℝ) := by
  -- 1. mun:multiply-le-nonneg, from H4
  have r160_1 : c ≥ 0 := by parley_side
  have s1 : x * (c : ℝ) ≤ y * (c : ℝ) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := x) (y := y) (c := (c : ℝ)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := x) (y := y) (c := (c : ℝ)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := x) (y := y) (c := (c : ℝ)) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := x) (y := y) (c := (c : ℝ)) (by parley_side) (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingMemberships.AMembershipBoundInARequiresLine
