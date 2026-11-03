module

public import Tactics

/-! Written from tests/elaborator/rows-read-either-way.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.RowsReadEitherWay.ARowMultipliedByANegativeNumberReadFromItsOtherSide

theorem a_row_multiplied_by_a_negative_number_read_from_its_other_side (x : ℝ) (hH2 : 4 * x - 5 ≤ 0) :
    0 ≤ -(8 * x) + 10 := by
  -- 1. inequalities
  have s1 : 0 ≤ -(8 * x) + 10 := by parley_order
  all_goals exact s1

end Parley.Tests.Elaborator.RowsReadEitherWay.ARowMultipliedByANegativeNumberReadFromItsOtherSide
