module

public import Tactics
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Int.Notation
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.Order.Interval.Finset.Defs
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalInARangeFromOne

theorem a_natural_in_a_range_from_one (m : ℤ) (hH1 : 0 ≤ m) (j : ℤ) (hH2 : 0 < j) (hH3 : j ≤ m + 1) :
    j ∈ Finset.Icc (1 : ℤ) (m + 1) := by
  -- 1. def:range-between k := j, a := 1, b := m + 1, from H2, H3
  exact ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m + 1))).mpr (by parley_side)

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalInARangeFromOne
