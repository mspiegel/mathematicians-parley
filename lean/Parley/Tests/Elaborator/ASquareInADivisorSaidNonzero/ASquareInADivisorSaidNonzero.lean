module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from tests/elaborator/a-square-in-a-divisor-said-nonzero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ASquareInADivisorSaidNonzero

theorem a_square_in_a_divisor_said_nonzero (x : ℝ) (y : ℝ) (hH3 : y = 1 / (1 + x ^ 2)) (hH4 : 1 / (1 + x ^ 2) ≥ 0) :
    y ≥ 0 := by
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))]
  -- 2. inequalities, from 1
  have s2 : 1 + x ^ 2 > 0 := by parley_side
  -- 3. transitivity, from H3, H4
  have r17_1 : 1 + x ^ 2 ≠ 0 := by parley_side
  have s3 : y ≥ 0 := by parley_side
  all_goals parley_side

end Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ASquareInADivisorSaidNonzero
