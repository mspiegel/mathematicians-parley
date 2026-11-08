module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-range-line-gives-its-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AnItemAsksARangeLinesBound

theorem an_item_asks_a_range_lines_bound (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) :
    (Set.Icc (1 : ℤ) k : Set ℤ) ⊆ (Set.Icc (1 : ℤ) n : Set ℤ) := by
  -- 1. mun:range-within a := 1, from H2
  exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := n) (by parley_set_side))

end Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AnItemAsksARangeLinesBound
