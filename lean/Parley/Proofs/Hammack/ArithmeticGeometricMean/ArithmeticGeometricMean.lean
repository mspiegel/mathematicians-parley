module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/hammack/arithmetic-geometric-mean.proof by parley build lean. -/

public section

namespace Parley.Proofs.Hammack.ArithmeticGeometricMean.ArithmeticGeometricMean

theorem arithmetic_geometric_mean (a : ℝ) (b : ℝ) (hH3 : a > 0) (hH4 : b > 0) :
    a + b ≥ 2 * Real.sqrt (a * b) := by
  -- 1. inequalities
  have s1 : a ≥ 0 := by parley_side
  -- 2. inequalities
  have s2 : b ≥ 0 := by parley_side
  -- 3. mun:product-nonneg x := a, y := b, from 1, 2
  have s3 : a * b ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := a) (y := b) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := a) (y := b) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := a) (y := b) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := a) (y := b) (by parley_side) (by parley_side)); parley_side)
  -- 4. def:sqrt x := a·b, from 3
  have s4a : Real.sqrt (a * b) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a * b) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a * b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a * b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a * b) (by parley_side)); parley_side)
  have s4b : Real.sqrt (a * b) ^ 2 = a * b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a * b) (by parley_side)); parley_side)
  -- 5. contradiction
  have s5 : a + b ≥ 2 * Real.sqrt (a * b) := by
    by_contra hc_hS
    have hS : ¬ a + b ≥ 2 * Real.sqrt (a * b) := by parley_suppose hc_hS
    -- 5.1. inequalities, from S, 4
    have s5_1 : a + b < 2 * Real.sqrt (a * b) := by parley_side
    -- 5.2. inequalities
    have s5_2 : 2 * Real.sqrt (a * b) ≥ 0 := by parley_side
    -- 5.3. inequalities, from H3, H4
    have s5_3 : a + b > 0 := by parley_side
    -- 5.4. inequalities
    have s5_4 : a + b ≥ 0 := by parley_side
    -- 5.5. mun:square-less x := a + b, y := 2·√(a·b), from 5.1, 5.2, 5.4
    have s5_5 : (a + b) ^ 2 < (2 * Real.sqrt (a * b)) ^ 2 := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_square_less (x := a + b) (y := 2 * Real.sqrt (a * b)) (by parley_side) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a + b) (y := 2 * Real.sqrt (a * b)) (by parley_side) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a + b) (y := 2 * Real.sqrt (a * b)) (by parley_side) (by parley_side))).mp (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_less (x := a + b) (y := 2 * Real.sqrt (a * b)) (by parley_side) (by parley_side))).mp (by parley_side); parley_side)
    -- 5.6. substitute
    have s5_6 : (a + b) ^ 2 < 4 * (a * b) := by
      have c1 : (2 * Real.sqrt (a * b)) ^ 2 = 4 * (a * b) := by linear_combination (norm := parley_norm) (4) * s4b
      have row1 : (a + b) ^ 2 < 4 * (a * b) := by parley_subst_at c1 s5_5
      exact row1
    -- 5.7. algebra
    have s5_7 : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by parley_ring
    -- 5.8. mun:square-nonneg x := a − b
    have s5_8 : (a - b) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a - b))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a - b)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a - b)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := a - b)); parley_side)
    -- 5.9. inequalities
    have s5_9 : (a + b) ^ 2 - 4 * (a * b) < 0 := by parley_side
    -- 5.10. transitivity, from 5.7, 5.9
    have s5_10 : (a - b) ^ 2 < 0 := by parley_side
    -- 5.11. inequalities, from 5.10
    have s5_11 : ¬ (a - b) ^ 2 ≥ 0 := by parley_side
    all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Hammack.ArithmeticGeometricMean.ArithmeticGeometricMean
