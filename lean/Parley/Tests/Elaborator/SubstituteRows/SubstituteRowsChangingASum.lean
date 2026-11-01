module

public import Parley.Library

/-! Written from tests/elaborator/substitute-rows.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsChangingASum

theorem substitute_rows_changing_a_sum (a : ℝ) (b : ℝ) (hH3 : a * 2 + b * 2 < 1) :
    2 * a + 2 * b < 1 := by
  -- 1. substitute
  have s1 : 2 * a + 2 * b < 1 := by
    have c1 : a * 2 + b * 2 = 2 * a + 2 * b := by parley_ring
    have row1 : 2 * a + 2 * b < 1 := by parley_subst_at c1 hH3
    exact row1
  all_goals parley_side

end Parley.Tests.Elaborator.SubstituteRows.SubstituteRowsChangingASum
