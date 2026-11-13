module

public import Tactics
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic.Linarith.Frontend
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
  have s1 : B - A ≥ 0 := by linarith only [hH6]
  -- 2. mun:product-nonneg x := B − A, y := C, from H7, 1
  have s2 : (B - A) * C ≥ 0 := by exact (Parley.Items.Stdlib.Numbers.mun_product_nonneg (x := B - A) (y := C) s1 hH7)
  -- 3. inequalities
  have s3 : A * C ≤ B * C := by linarith only [s2]
  -- 4. transitivity, from H5, H6
  have s4 : B > 0 := by exact lt_of_le_of_lt hH5 hH6
  -- 5. calculation
  calc A * C ≤ B * C := s3
    _ < B * D := by exact ((Parley.Items.Stdlib.Numbers.mun_less_scaled (x := C) (y := D) (c := B) s4)).mp hH8

end Parley.Proofs.Setmm.MultiplyingBounds.MultiplyingBounds
