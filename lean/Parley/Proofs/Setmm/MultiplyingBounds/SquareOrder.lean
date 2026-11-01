module

public import Parley.Items.Stdlib.Numbers
public import Parley.Library
public import Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds

/-! Written from proofs/setmm/multiplying-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MultiplyingBounds.SquareOrder

theorem square_order (A : ℝ) (B : ℝ) (hH3 : A ≥ 0) (hH4 : B ≥ 0) :
    (A < B ↔ A * A < B * B) := by
  -- the theorem. both directions
  have sThm : A < B ↔ A * A < B * B := by
    constructor
    · skip
      intro hD1
      -- 1. thm:multiplying-bounds C := A, D := B, from D1, H3
      have s1 : A * A < B * B := by first | linarith [(Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds.multiplying_bounds (A := A) (B := B) (C := A) (D := B) (by parley_side) (by parley_side) (by parley_side) (by parley_side))] | (have h := (Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds.multiplying_bounds (A := A) (B := B) (C := A) (D := B) (by parley_side) (by parley_side) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds.multiplying_bounds (A := A) (B := B) (C := A) (D := B) (by parley_side) (by parley_side) (by parley_side) (by parley_side))
      all_goals parley_side
    · skip
      intro hD2
      by_contra hc_hS
      have hS : ¬ A < B := by parley_suppose hc_hS
      -- 2. inequalities, from S
      have s2 : B ≤ A := by parley_side
      -- 3. inequalities
      have s3 : A - B ≥ 0 := by parley_side
      -- 4. mun:product-nonneg x := A − B, y := B, from H4, 3
      have s4 : (A - B) * B ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := B) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := B) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := B) (by parley_side) (by parley_side))
      -- 5. mun:product-nonneg x := A − B, y := A, from H3, 3
      have s5 : (A - B) * A ≥ 0 := by first | linarith [(Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := A) (by parley_side) (by parley_side))] | (have h := (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := A) (by parley_side) (by parley_side)); push_cast at h; linarith) | exact_mod_cast (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := A - B) (y := A) (by parley_side) (by parley_side))
      -- 6. inequalities
      have s6 : A * B - B * B ≥ 0 := by parley_side
      -- 7. inequalities
      have s7 : A * A - A * B ≥ 0 := by parley_side
      -- 8. inequalities, from 6, 7
      have s8 : A * A - B * B ≥ 0 := by parley_side
      -- 9. inequalities
      have s9 : B * B ≤ A * A := by parley_side
      -- 10. inequalities, from 9
      have s10 : ¬ A * A < B * B := by parley_side
      all_goals parley_side
  all_goals parley_side

end Parley.Proofs.Setmm.MultiplyingBounds.SquareOrder
