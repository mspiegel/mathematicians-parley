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

namespace Parley.Tests.Stdlib.Sums.RangeBetween

theorem range_between (k : ℤ) (a : ℤ) (b : ℤ) (hH4 : a ≤ k) (hH5 : k ≤ b) :
    k ∈ Finset.Icc a b := by
  -- 1. def:sums-range-between, from H4, H5
  exact ((Parley.Items.Stdlib.Sums.def_range_between (k := k) (a := a) (b := b))).mpr ⟨hH4, hH5⟩

end Parley.Tests.Stdlib.Sums.RangeBetween
