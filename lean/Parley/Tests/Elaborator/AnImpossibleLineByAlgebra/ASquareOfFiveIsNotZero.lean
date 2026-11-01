module

public import Parley.Library

/-! Written from tests/elaborator/an-impossible-line-by-algebra.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ASquareOfFiveIsNotZero

theorem a_square_of_five_is_not_zero (x : ℝ) (H2 : x ^ 2 = 5) :
    x ≠ 0 := by
  -- 1. contradiction
  have s1 : x ≠ 0 := by
    by_contra hc_S
    have S : x = 0 := by parley_suppose hc_S
    -- 1.1. algebra, from H2, S
    have s1_1 : (5 : ℝ) = 0 := by linear_combination (-1) * H2 + (x) * S
    exact absurd s1_1 (by norm_num)
    all_goals parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.AnImpossibleLineByAlgebra.ASquareOfFiveIsNotZero
