module

public import Tactics
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/identities/sqrt-of-sum-bound.proof by parley build lean. -/

public section

namespace Parley.Proofs.Identities.SqrtOfSumBound.SqrtOfSumBound

theorem sqrt_of_sum_bound (a : ℝ) (b : ℝ) (hH3 : a ≥ 0) (hH4 : b ≥ 0) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  -- 1. def:sqrt x := a, from H3
  have s1a : Real.sqrt a ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a) (by parley_side)); parley_side)
  have s1b : Real.sqrt a ^ 2 = a := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a) (by parley_side)); parley_side)
  -- 2. def:sqrt x := b, from H4
  have s2a : Real.sqrt b ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := b) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := b) (by parley_side)); parley_side)
  have s2b : Real.sqrt b ^ 2 = b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := b) (by parley_side)); parley_side)
  -- 3. inequalities, from H3, H4
  have s3 : a + b ≥ 0 := by parley_order
  -- 4. def:sqrt x := a + b, from 3
  have s4a : Real.sqrt (a + b) ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a + b) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a + b) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a + b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_2 (x := a + b) (by parley_side)); parley_side)
  have s4b : Real.sqrt (a + b) ^ 2 = a + b := by first | linear_combination (norm := parley_norm) (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)); (try push_cast at h); (try push_cast); linear_combination (norm := parley_norm) -h) | exact_mod_cast (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side))).symm | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)); rify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)); qify; linear_combination (norm := parley_norm) h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)); parley_int_power h) | (have h := (Parley.Items.Stdlib.Numbers.def_sqrt_3 (x := a + b) (by parley_side)); parley_side)
  -- 5. inequalities, from 1, 2
  have s5 : Real.sqrt a + Real.sqrt b ≥ 0 := by parley_order
  -- 6. mun:product-nonneg x := √a, y := √b, from 1, 2
  have s6 : Real.sqrt a * Real.sqrt b ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt a) (y := Real.sqrt b) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt a) (y := Real.sqrt b) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt a) (y := Real.sqrt b) (by parley_side) (by parley_side)) | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := Real.sqrt a) (y := Real.sqrt b) (by parley_side) (by parley_side)); parley_side)
  -- 7. inequalities
  have s7 : a + b ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by parley_order
  -- 8. calculation
  have s8 : Real.sqrt (a + b) ^ 2 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    calc Real.sqrt (a + b) ^ 2 = a + b := by parley_side
      _ ≤ a + b + 2 * (Real.sqrt a * Real.sqrt b) := by parley_side
      _ = (Real.sqrt a + Real.sqrt b) ^ 2 := by linear_combination (norm := parley_norm) (-1) * s1b + (-1) * s2b
  -- 9. mun:square-le x := √(a + b), y := √a + √b, from 1, 2, 4, 5, 8
  have s9 : Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by first | (assumption; done) | exact ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (a + b)) (y := Real.sqrt a + Real.sqrt b) (by parley_side) (by parley_side))).mpr (by parley_side) | (have h := ((Parley.Items.Stdlib.Numbers.mun_square_le (x := Real.sqrt (a + b)) (y := Real.sqrt a + Real.sqrt b) (by parley_side) (by parley_side))).mpr (by parley_side); parley_side)
  all_goals parley_side

end Parley.Proofs.Identities.SqrtOfSumBound.SqrtOfSumBound
