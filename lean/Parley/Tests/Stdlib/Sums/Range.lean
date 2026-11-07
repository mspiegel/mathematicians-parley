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

namespace Parley.Tests.Stdlib.Sums.Range

theorem range (n : ℤ) (k : ℤ) (hH3 : k ∈ Finset.Icc (1 : ℤ) n) :
    (0 < k ∧ k ≤ n) := by
  -- 1. def:sums-range, from H3
  have s1 : 0 < k ∧ k ≤ n := by first | exact ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n))).mp (by parley_side) | exact_mod_cast ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range (k := k) (n := n))).mp (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Stdlib.Sums.Range
