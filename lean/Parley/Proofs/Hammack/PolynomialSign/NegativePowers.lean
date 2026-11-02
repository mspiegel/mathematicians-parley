module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/polynomial-sign.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.PolynomialSign.NegativePowers

theorem negative_powers (x : ℝ) (hH2 : x < 0) :
    x ^ 2 ≥ 0 ∧ x ^ 3 ≤ 0 ∧ x ^ 4 ≥ 0 ∧ x ^ 5 ≤ 0 := by
  -- 1. inequalities
  have s1 : -x ≥ 0 := by parley_side
  -- 2. mun:square-nonneg
  have s2 : x ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x))
  -- 3. mun:product-nonneg x := x², y := −x, from 1, 2
  have s3 : x ^ 2 * -x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 2) (y := -x) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 2) (y := -x) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 2) (y := -x) (by parley_side) (by parley_side))
  -- 4. inequalities
  have s4 : x ^ 3 ≤ 0 := by parley_side
  -- 5. mun:square-nonneg x := x²
  have s5 : (x ^ 2) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x ^ 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x ^ 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := x ^ 2))
  -- 6. algebra
  have s6 : x ^ 4 = (x ^ 2) ^ 2 := by parley_ring
  -- 7. transitivity, from 6, 5
  have s7 : x ^ 4 ≥ 0 := by parley_side
  -- 8. mun:product-nonneg x := x⁴, y := −x, from 1, 7
  have s8 : x ^ 4 * -x ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 4) (y := -x) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 4) (y := -x) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := x ^ 4) (y := -x) (by parley_side) (by parley_side))
  -- 9. inequalities
  have s9 : x ^ 5 ≤ 0 := by parley_side
  -- 10. join 2, 4, 7, 9
  have s10a : x ^ 2 ≥ 0 := by parley_side
  have s10b : x ^ 3 ≤ 0 := by parley_side
  have s10c : x ^ 4 ≥ 0 := by parley_side
  have s10d : x ^ 5 ≤ 0 := by parley_side
  exact ⟨by parley_side, by parley_side, by parley_side, by parley_side⟩

end Parley.Proofs.Hammack.PolynomialSign.NegativePowers
