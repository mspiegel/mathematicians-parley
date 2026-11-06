module

public import Tactics
public import Parley.Items.Stdlib.Sums

/-! Written from tests/elaborator/a-natural-is-at-least-one-cited.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalInARangeFromOne

theorem a_natural_in_a_range_from_one (m : ℤ) (hH1 : 0 ≤ m) (j : ℤ) (hH2 : 0 < j) (hH3 : j ≤ m + 1) :
    j ∈ Finset.Icc (1 : ℤ) (m + 1) := by
  -- 1. def:range-between k := j, a := 1, b := m + 1, from H2, H3
  have s1 : j ∈ Finset.Icc (1 : ℤ) (m + 1) := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m + 1))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Sums.def_range_between (k := j) (a := (1 : ℤ)) (b := m + 1))).mpr (by parley_side); parley_side)
  all_goals exact s1

end Parley.Tests.Elaborator.ANaturalIsAtLeastOneCited.ANaturalInARangeFromOne
