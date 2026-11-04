module

public import AlgebraTactics
public import OrderTactics
public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/product-step-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ProductStepBound.ProductStepBound

theorem product_step_bound (t : ℝ) (p : ℝ) (hH3 : 0 < t) (hH4 : t ≤ 1 / 4) (hH5 : p ≥ 1 / 4 + t) :
    p * (1 - t) ≥ 1 / 4 + t / 2 := by
  -- 1. inequalities
  have s1 : 3 / 4 ≤ 1 - t := by parley_order
  -- 2. inequalities, from 1
  have s2 : 0 < 1 - t := by parley_order
  -- 3. mun:multiply-le x := 1/4 + t, y := p, c := 1 − t, from H5, 2
  have s3 : (1 - t) * (1 / 4 + t) ≤ (1 - t) * p := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_multiply_le (x := 1 / 4 + t) (y := p) (c := 1 - t) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := 1 / 4 + t) (y := p) (c := 1 - t) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := 1 / 4 + t) (y := p) (c := 1 - t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_multiply_le (x := 1 / 4 + t) (y := p) (c := 1 - t) (by parley_side) (by parley_side)); parley_side)
  -- 4. algebra
  have s4 : (1 - t) * (1 / 4 + t) = 1 / 4 + t / 2 + t * (1 / 4 - t) := by parley_ring
  -- 5. inequalities
  have s5 : 0 ≤ 1 / 4 - t := by parley_order
  -- 6. inequalities
  have s6 : t ≥ 0 := by parley_order
  -- 7. mun:product-nonneg x := t, y := 1/4 − t, from 5, 6
  have s7 : t * (1 / 4 - t) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := t) (y := 1 / 4 - t) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := t) (y := 1 / 4 - t) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := t) (y := 1 / 4 - t) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := t) (y := 1 / 4 - t) (by parley_side) (by parley_side)); parley_side)
  -- 8. inequalities
  have s8 : 1 / 4 + t / 2 + t * (1 / 4 - t) ≥ 1 / 4 + t / 2 := by parley_order
  -- 9. algebra
  have s9 : p * (1 - t) = (1 - t) * p := by parley_ring
  -- 10. transitivity, from 9, 3, 4, 8
  have s10 : p * (1 - t) ≥ 1 / 4 + t / 2 := by parley_order
  all_goals exact s10

end Parley.Proofs.Hammack.ProductStepBound.ProductStepBound
