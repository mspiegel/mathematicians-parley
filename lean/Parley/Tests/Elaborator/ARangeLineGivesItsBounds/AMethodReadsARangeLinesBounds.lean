module

public import Parley.Library

/-! Written from tests/elaborator/a-range-line-gives-its-bounds.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AMethodReadsARangeLinesBounds

theorem a_method_reads_a_range_lines_bounds (n : ℤ) (k : ℤ) (hH2 : k ∈ Finset.Icc (2 : ℤ) n) :
    0 < k := by
  -- 1. inequalities, from H2
  have s1 : 0 < k := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ARangeLineGivesItsBounds.AMethodReadsARangeLinesBounds
