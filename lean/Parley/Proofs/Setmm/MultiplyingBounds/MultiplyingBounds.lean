module

public import LeanBridges
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/multiplying-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds

theorem multiplying_bounds (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (hH5 : 0 ≤ A) (hH6 : A < B) (hH7 : 0 ≤ C) (hH8 : C < D) :
    A * C < B * D := by
  -- 1. inequalities
  have s1 : B - A ≥ 0 := by parley_side
  -- 2. mun:product-nonneg x := B − A, y := C, from H7, 1
  have s2 : (B - A) * C ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := B - A) (y := C) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := B - A) (y := C) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := B - A) (y := C) (by parley_side) (by parley_side))
  -- 3. inequalities
  have s3 : A * C ≤ B * C := by parley_side
  -- 4. transitivity, from H5, H6
  have s4 : B > 0 := by parley_side
  -- 5. calculation
  have s5 : A * C < B * D := by
    calc A * C ≤ B * C := by parley_side
      _ < B * D := by first | linarith [((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := C) (y := D) (c := B) (by parley_side))).mp (by parley_side)] | (have h := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := C) (y := D) (c := B) (by parley_side))).mp (by parley_side); push_cast at h; linarith) | exact_mod_cast ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := C) (y := D) (c := B) (by parley_side))).mp (by parley_side)
  all_goals parley_side

end Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds
