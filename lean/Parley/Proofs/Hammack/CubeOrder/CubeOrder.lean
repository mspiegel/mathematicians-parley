module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/cube-order.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeOrder.CubeOrder

theorem cube_order (x : ℝ) (y : ℝ) (hH3 : x ^ 3 < y ^ 3) :
    x < y := by
  -- the theorem. contradiction
  have sThm : x < y := by
    by_contra hc_hS
    have hS : ¬ x < y := by parley_suppose hc_hS
    -- 1. inequalities, from S
    have s1 : y ≤ x := by parley_side
    -- 2. inequalities
    have s2 : x - y ≥ 0 := by parley_side
    -- 3. mun:square-nonneg x := x + y/2
    have s3 : (x + y / 2) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x + y / 2))
    -- 4. mun:square-nonneg x := y
    have s4 : y ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := y))
    -- 5. inequalities
    have s5 : 3 * y ^ 2 / 4 ≥ 0 := by parley_side
    -- 6. inequalities, from 3, 5
    have s6 : (x + y / 2) ^ 2 + 3 * y ^ 2 / 4 ≥ 0 := by parley_side
    -- 7. algebra
    have s7 : x ^ 2 + x * y + y ^ 2 = (x + y / 2) ^ 2 + 3 * y ^ 2 / 4 := by parley_ring
    -- 8. transitivity, from 7, 6
    have s8 : x ^ 2 + x * y + y ^ 2 ≥ 0 := by parley_side
    -- 9. mun:product-nonneg x := x − y, y := x² + x·y + y², from 2, 8
    have s9 : (x - y) * (x ^ 2 + x * y + y ^ 2) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x - y) (y := x ^ 2 + x * y + y ^ 2) (by parley_side) (by parley_side))
    -- 10. algebra
    have s10 : x ^ 3 - y ^ 3 = (x - y) * (x ^ 2 + x * y + y ^ 2) := by parley_ring
    -- 11. transitivity, from 10, 9
    have s11 : x ^ 3 - y ^ 3 ≥ 0 := by parley_side
    -- 12. inequalities
    have s12 : x ^ 3 ≥ y ^ 3 := by parley_side
    -- 13. inequalities, from 12
    have s13 : ¬ x ^ 3 < y ^ 3 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CubeOrder.CubeOrder
