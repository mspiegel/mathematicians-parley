module

public import Parley.Library

/-! Written from tests/elaborator/an-impossible-line-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ANumberEqualToARootIsNotOne

theorem a_number_equal_to_a_root_is_not_one (x : ℝ) (H2 : x = Real.sqrt (2 : ℝ)) :
    x ≠ 1 := by
  -- 1. contradiction
  have s1 : x ≠ 1 := by
    by_contra hc_S
    have S : x = 1 := by parley_suppose hc_S
    -- 1.1. algebra, from H2, S
    have s1_1 : Real.sqrt (2 : ℝ) - 1 = 0 := by linear_combination (-1) * H2 + S
    exact absurd s1_1 (by norm_num)
    parley_side
  parley_side

end Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ANumberEqualToARootIsNotOne
