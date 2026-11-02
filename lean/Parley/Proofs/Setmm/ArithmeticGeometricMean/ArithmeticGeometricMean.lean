module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/arithmetic-geometric-mean.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.ArithmeticGeometricMean.ArithmeticGeometricMean

theorem arithmetic_geometric_mean (A : ℝ) (B : ℝ) (hH3 : A ≥ 0) (hH4 : B ≥ 0) :
    Real.sqrt (A * B) ≤ (A + B) / 2 := by
  -- 1. mun:product-nonneg x := A, y := B, from H3, H4
  have s1 : A * B ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A) (y := B) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A) (y := B) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A) (y := B) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A) (y := B) (by parley_side) (by parley_side)); parley_side)
  -- 2. def:sqrt x := A·B, from 1
  have s2 : Real.sqrt (A * B) ^ 2 = A * B := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := A * B) (by parley_side)); parley_side)
  -- 3. def:sqrt x := A·B, from 1
  have s3 : Real.sqrt (A * B) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A * B) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A * B) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A * B) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := A * B) (by parley_side)); parley_side)
  -- 4. inequalities, from H3, H4
  have s4 : A + B ≥ 0 := by parley_order
  -- 5. inequalities
  have s5 : (A + B) / 2 ≥ 0 := by parley_order
  -- 6. algebra
  have s6 : ((A + B) / 2) ^ 2 = A * B + ((A - B) / 2) ^ 2 := by parley_ring
  -- 7. mun:square-nonneg x := (A − B)/2
  have s7 : ((A - B) / 2) ^ 2 ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (A - B) / 2))] | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (A - B) / 2)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (A - B) / 2)) | (have h := (Parley.Items.Stdlib.Numbers.mun_square_nonneg (x := (A - B) / 2)); parley_side)
  -- 8. inequalities
  have s8 : A * B ≤ A * B + ((A - B) / 2) ^ 2 := by parley_order
  -- 9. transitivity, from 2, 8, 6
  have s9 : Real.sqrt (A * B) ^ 2 ≤ ((A + B) / 2) ^ 2 := by parley_order
  -- 10. mun:square-le x := √(A·B), y := (A + B)/2, from 3, 5, 9
  have s10 : Real.sqrt (A * B) ≤ (A + B) / 2 := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (A * B)) (y := (A + B) / 2) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (A * B)) (y := (A + B) / 2) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.ArithmeticGeometricMean.ArithmeticGeometricMean
