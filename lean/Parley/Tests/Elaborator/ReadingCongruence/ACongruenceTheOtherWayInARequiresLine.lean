module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Divisibility

/-! Written from tests/elaborator/reading-congruence.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayInARequiresLine

theorem a_congruence_the_other_way_in_a_requires_line (n : ℤ) (hH1 : 0 < n) (x : ℤ) (hH2 : x ∈ Finset.Icc (0 : ℤ) (n - 1)) (y : ℤ) (hH3 : y ∈ Finset.Icc (0 : ℤ) (n - 1)) (hH4 : y ≡ x [ZMOD n]) :
    x = y := by
  -- 1. mun:congruent-in-range, from H2, H3
  have r41_1 : x ≡ y [ZMOD n] := by parley_side
  have s1 : x = y := by exact (Parley.Items.Stdlib.Divisibility.mun_congruent_in_range (n := n) (by parley_side) (x := x) hH2 (y := y) hH3 (by parley_side))
  all_goals exact s1

end Parley.Tests.Elaborator.ReadingCongruence.ACongruenceTheOtherWayInARequiresLine
