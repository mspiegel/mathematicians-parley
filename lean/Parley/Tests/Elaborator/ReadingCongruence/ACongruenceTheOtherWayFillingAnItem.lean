module

public import PowerTactics
public import Tactics
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Qify
public import Mathlib.Tactic.Rify
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayFillingAnItem

theorem a_congruence_the_other_way_filling_an_item (n : ℤ) (hH1 : 0 < n) (x : ℤ) (hH2 : x ∈ Finset.Icc (0 : ℤ) (n - 1)) (y : ℤ) (hH3 : y ∈ Finset.Icc (0 : ℤ) (n - 1)) (hH4 : y ≡ x [ZMOD n]) :
    x = y := by
  -- 1. mun:congruent-in-range, from H2, H3, H4
  have s1 : x = y := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side)); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayFillingAnItem
