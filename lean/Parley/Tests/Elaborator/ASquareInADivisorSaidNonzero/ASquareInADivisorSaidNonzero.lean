module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith.Frontend
public import Parley.Items.Stdlib.Numbers

/-! Written from tests/elaborator/a-square-in-a-divisor-said-nonzero.proof by parley build lean. -/

public section

namespace Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ASquareInADivisorSaidNonzero

theorem a_square_in_a_divisor_said_nonzero (x : ℝ) (y : ℝ) (hH3 : y = 1 / (1 + x ^ 2)) (hH4 : 1 / (1 + x ^ 2) ≥ 0) :
    y ≥ 0 := by
  -- 1. mun:square-nonneg
  have s1 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_side)
  -- 2. inequalities, from 1
  have s2 : 1 + x ^ 2 > 0 := by parley_order
  -- 3. transitivity, from H3, H4
  have r17_1 : 1 + x ^ 2 ≠ 0 := by parley_side
  have s3 : y ≥ 0 := by parley_order
  all_goals exact s3

end Parley.Tests.Elaborator.ASquareInADivisorSaidNonzero.ASquareInADivisorSaidNonzero
