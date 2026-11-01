module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library

/-! Written from proofs/hammack/cube-root-injective.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.CubeRootInjective.CubeInjective

theorem cube_injective (a : ℝ) (b : ℝ) (hH3 : a ^ 3 = b ^ 3) :
    a = b := by
  -- the theorem. contradiction
  have sThm : a = b := by
    by_contra hc_hS
    have hS : a ≠ b := by parley_suppose hc_hS
    -- 1. mun:square-positive x := a − b
    have r19_1 : a - b ≠ 0 := by parley_side
    have s1 : (a - b) ^ 2 > 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_positive (x := a - b) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_positive (x := a - b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_positive (x := a - b) (by parley_side))
    -- 2. mun:square-nonneg x := a + b
    have s2 : (a + b) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a + b))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a + b)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a + b))
    -- 3. inequalities
    have s3 : 3 * (a + b) ^ 2 ≥ 0 := by parley_side
    -- 4. inequalities, from 1, 3
    have s4 : (a - b) ^ 2 + 3 * (a + b) ^ 2 > 0 := by parley_side
    -- 5. algebra, from H3
    have s5 : (a - b) * (a ^ 2 + a * b + b ^ 2) = 0 := by linear_combination (norm := parley_norm) hH3
    -- 6. mun:zero-product x := a − b, y := a² + a·b + b², from 5
    have s6 : a - b = 0 ∨ a ^ 2 + a * b + b ^ 2 = 0 := by first | exact ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := a - b) (y := a ^ 2 + a * b + b ^ 2))).mp (by parley_side) | exact (((Parley.Items.Stdlib.Numbers.mun_zero_product (x := a - b) (y := a ^ 2 + a * b + b ^ 2))).mp (by parley_side)).symm | simpa using ((Parley.Items.Stdlib.Numbers.mun_zero_product (x := a - b) (y := a ^ 2 + a * b + b ^ 2))).mp (by parley_side)
    -- 7. cases, from 6
    have s7 : a ^ 2 + a * b + b ^ 2 = 0 := by
      rcases s6 with hC1 | hC2
      · skip
        -- 7.1. algebra, from C1
        have s7_1 : a = b := by linear_combination (norm := parley_norm) hC1
        all_goals parley_side
      · skip
        all_goals parley_side
    -- 8. algebra, from 7
    have s8 : (a - b) ^ 2 + 3 * (a + b) ^ 2 = 0 := by linear_combination (norm := parley_norm) (4) * s7
    -- 9. inequalities
    have s9 : (a - b) ^ 2 + 3 * (a + b) ^ 2 ≤ 0 := by parley_side
    -- 10. inequalities, from 9
    have s10 : ¬ (a - b) ^ 2 + 3 * (a + b) ^ 2 > 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.CubeRootInjective.CubeInjective
