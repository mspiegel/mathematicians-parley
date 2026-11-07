module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Parley.Items.Stdlib.Sums

/-! Written from tests/stdlib/sums.proof by parley build lean. -/

public section

namespace Parley.Tests.Stdlib.Sums.RangeNat0

theorem range_nat0 (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (0 : ℤ) n) :
    0 ≤ k := by
  -- 1. mun:sums-range-nat0, from H2
  have s1 : 0 ≤ k := by exact (Parley.Items.Stdlib.Sums.mun_range_nat0 (n := n) (k := k) hH2)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.RangeNat0
