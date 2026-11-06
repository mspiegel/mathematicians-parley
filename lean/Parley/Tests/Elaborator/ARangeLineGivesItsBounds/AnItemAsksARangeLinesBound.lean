module

public import SetTactics
public import Tactics
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Tactic.SetNotationForOrder
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-range-line-gives-its-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AnItemAsksARangeLinesBound

theorem an_item_asks_a_range_lines_bound (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (1 : ℤ) n) :
    (Set.Icc (1 : ℤ) k : Set ℤ) ⊆ (Set.Icc (1 : ℤ) n : Set ℤ) := by
  -- 1. mun:range-within a := 1, from H2
  have s1 : (Set.Icc (1 : ℤ) k : Set ℤ) ⊆ (Set.Icc (1 : ℤ) n : Set ℤ) := by first | exact (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := n) (by parley_set_side)) | exact ((Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := n) (by parley_set_side))).symm | simpa using (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := n) (by parley_set_side)) | exact_mod_cast (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := n) (by parley_set_side)) | (have h := (Parley.Items.Stdlib.Sums.mun_range_within (a := (1 : ℤ)) (k := k) (n := n) (by parley_set_side)); parley_set_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AnItemAsksARangeLinesBound
