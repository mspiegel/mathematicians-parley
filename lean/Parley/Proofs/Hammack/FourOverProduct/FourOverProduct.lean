module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/four-over-product.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.FourOverProduct.FourOverProduct

theorem four_over_product (x : ℝ) (hH2 : 0 < x) (hH3 : x < 4) :
    4 / (x * (4 - x)) ≥ 1 := by
  -- 1. inequalities
  have s1 : 0 < 4 - x := by parley_side
  -- 2. mun:less-scaled x := 0, y := 4 − x, c := x, from H2, 1
  have s2 : x * 0 < x * (4 - x) := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := 4 - x) (c := x) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := 4 - x) (c := x) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := (0 : ℝ)) (y := 4 - x) (c := x) (by parley_side))).mp (by parley_side)
  -- 3. inequalities, from 2
  have s3 : 0 < x * (4 - x) := by parley_side
  -- 4. mun:square-nonneg x := x − 2
  have s4 : (x - 2) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x - 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x - 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x - 2))
  -- 5. algebra
  have s5 : (x - 2) ^ 2 = 4 - x * (4 - x) := by parley_ring
  -- 6. transitivity, from 4, 5
  have s6 : 0 ≤ 4 - x * (4 - x) := by parley_side
  -- 7. inequalities
  have s7 : x * (4 - x) ≤ 4 := by parley_side
  -- 8. mun:divide-le x := x·(4 − x), y := 4, c := x·(4 − x), from 3, 7
  have s8 : x * (4 - x) / (x * (4 - x)) ≤ 4 / (x * (4 - x)) := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_divide_le (x := x * (4 - x)) (y := (4 : ℝ)) (c := x * (4 - x)) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_divide_le (x := x * (4 - x)) (y := (4 : ℝ)) (c := x * (4 - x)) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_divide_le (x := x * (4 - x)) (y := (4 : ℝ)) (c := x * (4 - x)) (by parley_side) (by parley_side))
  -- 9. algebra
  have r42_1 : 0 ≠ x * (4 - x) := by parley_side
  have s9 : x * (4 - x) / (x * (4 - x)) = 1 := by parley_ring
  -- 10. transitivity, from 9, 8
  have r46_1 : 0 ≠ x * (4 - x) := by parley_side
  have s10 : 4 / (x * (4 - x)) ≥ 1 := by parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.FourOverProduct.FourOverProduct
