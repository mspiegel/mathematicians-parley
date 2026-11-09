module

public import OrderTactics
public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.Positivity.Basic
public import Parley.Items.Stdlib.Numbers

/-! Written from proofs/setmm/multiplying-bounds.proof by parley build lean. -/

public section

namespace Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds

theorem multiplying_bounds (A : ℝ) (B : ℝ) (C : ℝ) (D : ℝ) (hH5 : 0 ≤ A) (hH6 : A < B) (hH7 : 0 ≤ C) (hH8 : C < D) :
    A * C < B * D := by
  -- 1. inequalities
  have s1 : B - A ≥ 0 := by parley_order
  -- 2. mun:product-nonneg x := B − A, y := C, from H7, 1
  have s2 : (B - A) * C ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := B - A) (y := C) (by parley_side) (by parley_side))
  -- 3. inequalities
  have s3 : A * C ≤ B * C := by parley_order
  -- 4. transitivity, from H5, H6
  have s4 : B > 0 := by parley_order
  -- 5. calculation
  calc A * C ≤ B * C := by parley_side
    _ < B * D := ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := C) (y := D) (c := B) (by parley_side))).mp hH8

end Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds
