module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/cubic-above-minus-one.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubicAboveMinusOne.CubicAboveMinusOne

theorem cubic_above_minus_one (x : ℝ) (hH2 : x ^ 3 - x > 0) :
    x > -1 := by
  -- the theorem. contradiction
  have sThm : x > -1 := by
    by_contra hc_hS
    have hS : ¬ x > -1 := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : x ≤ -1 := by parley_side
    -- 2. mun:square-nonneg
    have s2 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); parley_side)
    -- 3. inequalities
    have s3 : -x ≥ 1 := by parley_side
    -- 4. inequalities, from 2, 3
    have s4 : x ^ 2 - x > 0 := by parley_side
    -- 5. inequalities, from 1
    have s5 : x + 1 ≤ 0 := by parley_side
    -- 6. mun:multiply-le x := x + 1, y := 0, c := x² − x, from 4, 5
    have s6 : (x ^ 2 - x) * (x + 1) ≤ (x ^ 2 - x) * 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := x + 1) (y := (0 : ℝ)) (c := x ^ 2 - x) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := x + 1) (y := (0 : ℝ)) (c := x ^ 2 - x) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := x + 1) (y := (0 : ℝ)) (c := x ^ 2 - x) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := x + 1) (y := (0 : ℝ)) (c := x ^ 2 - x) (by parley_side) (by parley_side)); parley_side)
    -- 7. inequalities
    have s7 : x ^ 3 - x ≤ 0 := by parley_side
    -- 8. inequalities, from 7
    have s8 : ¬ x ^ 3 - x > 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CubicAboveMinusOne.CubicAboveMinusOne
