module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/reading-memberships.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLine

theorem a_range_bound_in_a_requires_line (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) (c : ℝ) (hH4 : c ≥ 0) :
    (k : ℝ) * c ≤ (n : ℝ) * c := by
  -- 1. mun:multiply-le-nonneg, from H4
  have r41_1 : k ≤ n := by parley_side
  exact (Parley.Items.Stdlib.Numbers.mun_multiply_le_nonneg (x := (k : ℝ)) (y := (n : ℝ)) (c := c) (by parley_side) (by parley_side))

end Parley.Tests.Elaborator.ReadingMemberships.ARangeBoundInARequiresLine
